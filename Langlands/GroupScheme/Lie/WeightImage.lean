import Langlands.GroupScheme.Lie.Functoriality

/-! # Nonzero character weights in actual subgroup Lie images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}}
  {T : CommGroupScheme (Spec R)}
  {H B G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- The actual Lie image of `i` contains a nonzero vector of character weight `α`
for the action through `j`. -/
def MeetsWeightSpace (j : T.toGrp ⟶ G) (i : H ⟶ G)
    (α : characterLattice T) : Prop :=
  ∃ X ∈ weightSpace j α, X ≠ 0 ∧
    ∃ Y : lieKernel H R, Y.val ≫ i.hom.hom = X.toMul.val

/-- A factorization of subgroup morphisms preserves a nonzero ambient Lie witness. -/
theorem MeetsWeightSpace.of_factorization (j : T.toGrp ⟶ G)
    (i : H ⟶ G) (b : B ⟶ G) (f : H ⟶ B) (hf : f ≫ b = i)
    (α : characterLattice T) (h : MeetsWeightSpace j i α) :
    MeetsWeightSpace j b α := by
  obtain ⟨X, hX, hne, Y, hY⟩ := h
  refine ⟨X, hX, hne, targetMap f R Y, ?_⟩
  change (Y.val ≫ f.hom.hom) ≫ b.hom.hom = X.toMul.val
  rw [Category.assoc]
  change Y.val ≫ (f ≫ b).hom.hom = X.toMul.val
  rw [hf]
  exact hY

/-- Composition of the subgroup morphism enlarges its Lie image. -/
theorem MeetsWeightSpace.comp (j : T.toGrp ⟶ G) (b : B ⟶ G)
    (f : H ⟶ B) (α : characterLattice T)
    (h : MeetsWeightSpace j (f ≫ b) α) :
    MeetsWeightSpace j b α :=
  h.of_factorization j (f ≫ b) b f rfl α

end Langlands.GroupScheme.Lie
