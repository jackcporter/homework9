import Sets.Basic

open Set

variable (α β : Type)
variable (X Y Z : Set α)
variable (W : Set β) 

example : X ⊆ X := by
  intro x
  intro h
  exact h

example : X ⊆ X := fun _ h => h

#check @set_ext α X Y

example (h : X = Y) : X ∪ Z = Y ∪ Z := by
  set_extensionality x
  · intro g
    apply Or.elim g
    rotate_left
    · exact fun h => Or.inr h  
    · intro g₁
      have : x ∈ Y := by
        apply (set_ext.mp h g₁).mp
      exact Or.inl this


theorem problem1 : ∅ ∈ 𝒫  X := sorry 

theorem problem2 (U : β → Set α) : ∀ b, U b ⊆ BigUnion U := sorry 

theorem problem3 (h : X ⊆ Y) : (X ×ˢ W) ⊆ (Y ×ˢ W) := sorry

theorem problem4 (h : Y ∩ Z = ∅) : Yᶜ ∪ Zᶜ = Univ := sorry 

theorem problem5 : (X \ Y) ∪ (Y \ X) = (X ∪ Y) \ (X ∩ Y) := sorry 
