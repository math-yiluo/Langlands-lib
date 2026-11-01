import Langlands.AlgebraicGeometry.FiniteEtale.GeometricCardinality
import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Langlands.AbelianScheme.Tate.Integral

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.Tate

variable {K : Type u} [Field K] (B : AbelianScheme (Spec (.of K))) (n : ℕ)

/-- The actual coordinate algebra of the multiplication kernel. -/
abbrev torsionCoordinates : Type u :=
  Γ((GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.left, ⊤)

/-- The scalar structure induced by the structure morphism of the actual kernel. -/
abbrev torsionCoordinatesAlgebra : Algebra K (torsionCoordinates B n) :=
  Langlands.AlgebraicGeometry.FiniteEtale.coordinateAlgebra
    (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom

/-- Actual sections of the actual kernel identify with its already defined torsion level. -/
def torsionSectionsEquiv :
    {x : Spec (.of K) ⟶ (GroupScheme.kernel
      (GroupScheme.multiplication B.toGrp (n : ℤ))).X.left //
      x ≫ (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom = 𝟙 _} ≃
      GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n := by
  let T := (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X
  let e : {x : Spec (.of K) ⟶ T.left // x ≫ T.hom = 𝟙 _} ≃
      (Over.mk (𝟙 (Spec (.of K))) ⟶ T) :=
    { toFun := fun x => Over.homMk x.val x.property
      invFun := fun x => ⟨x.left, by simp⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => by apply Over.OverMorphism.ext; rfl }
  exact e.trans (Additive.ofMul.trans
    (GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n).toEquiv)

/-- At an invertible level over a separably closed field, the actual torsion-point count
is exactly the dimension of the actual kernel coordinate algebra. -/
theorem natCard_level_eq_finrank [IsSepClosed K] (hn : (n : K) ≠ 0) :
    letI := torsionCoordinatesAlgebra B n
    Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n) =
      Module.finrank K (torsionCoordinates B n) := by
  let := torsionCoordinatesAlgebra B n
  have := multiplicationKernel_isFinite_of_ne_zero B n hn
  have := multiplicationKernel_etale_of_ne_zero B n hn
  exact (Nat.card_congr (torsionSectionsEquiv B n).symm).trans
    (Langlands.AlgebraicGeometry.FiniteEtale.natCard_sections_eq_finrank
      (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom)

end Langlands.AbelianScheme.Tate
