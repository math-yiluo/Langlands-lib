import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.KernelBaseChange

/-! # Base change of the actual special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear

variable (n : Type) [Fintype n] [DecidableEq n]
variable {R R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)

/-- On every test scheme, the pullback model and the model over the new base
have the same determinant-one matrices of global sections. -/
def baseChangeModelPointsEquiv (T : Over (Spec R')) :
    (T ⟶ ((GroupScheme.baseChange b).obj (groupScheme n R)).X) ≃*
      (T ⟶ (groupScheme n R').X) :=
  ((baseChangePointsEquiv b (groupScheme n R) T).trans
    (pointsEquiv n R ((Over.map b).obj T))).trans (pointsEquiv n R' T).symm

theorem baseChangeModelPointsEquiv_naturality {T T' : Over (Spec R')}
    (a : T' ⟶ T) (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme n R)).X) :
    baseChangeModelPointsEquiv n b T' (a ≫ x) =
      a ≫ baseChangeModelPointsEquiv n b T x := by
  apply (pointsEquiv n R' T').injective
  simp only [baseChangeModelPointsEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
    pointsEquiv_naturality]
  rfl

/-- The actual special linear model commutes with arbitrary change of the affine base. -/
def baseChangeModelIso :
    (GroupScheme.baseChange b).obj (groupScheme n R) ≅ groupScheme n R' :=
  isoOfPoints (baseChangeModelPointsEquiv n b)
    (baseChangeModelPointsEquiv_naturality n b)

/-- The model comparison preserves all entries on every relative test scheme. -/
theorem pointsEquiv_baseChangeModelIso_hom (T : Over (Spec R'))
    (x : T ⟶ ((GroupScheme.baseChange b).obj (groupScheme n R)).X) :
    pointsEquiv n R' T (x ≫ (baseChangeModelIso n b).hom.hom.hom) =
      pointsEquiv n R ((Over.map b).obj T) (baseChangePointsEquiv b _ T x) := by
  rw [baseChangeModelIso, comp_isoOfPoints_hom]
  exact (pointsEquiv n R' T).apply_symm_apply _

end Langlands.GroupScheme.SpecialLinear
