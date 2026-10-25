import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.GeneralLinearContragredient
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.RepresentationTheory.Intertwining

/-! # Dual coefficients of actual group-scheme matrix representations -/

noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
variable {n : Type} [Fintype n] [DecidableEq n]

/-- The dual coordinate representation is an actual composite of group-scheme morphisms. -/
def dual (ρ : MatrixRepresentation G n) : MatrixRepresentation G n :=
  ρ ≫ (GeneralLinear.contragredientIso n R).hom

@[simp] theorem dual_dual (ρ : MatrixRepresentation G n) : ρ.dual.dual = ρ := by
  simp only [dual, Category.assoc, GeneralLinear.contragredientIso_hom_comp,
    Category.comp_id]

@[simp] theorem dual_restrict (ρ : MatrixRepresentation G n) (f : H ⟶ G) :
    (ρ.restrict f).dual = ρ.dual.restrict f :=
  Category.assoc f ρ _

@[simp] theorem dual_pointMatrix (ρ : MatrixRepresentation G n) (T : Over (Spec R))
    (x : T ⟶ G.X) :
    ρ.dual.pointMatrix T x =
      GeneralLinear.matrixContragredient n Γ(T.left, ⊤) (ρ.pointMatrix T x) := by
  simp only [pointMatrix_apply, dual, Grp.comp_hom_hom, ← Category.assoc]
  exact GeneralLinear.pointsEquiv_contragredientIso n R T _

@[simp] theorem dual_affineMatrix (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) :
    ρ.dual.affineMatrix S x =
      GeneralLinear.matrixContragredient n S (ρ.affineMatrix S x) := by
  simp only [affineMatrix_apply, dual, Grp.comp_hom_hom, ← Category.assoc]
  exact GeneralLinear.affinePointsEquiv_contragredientIso n R S _

/-- The dual coordinate action is multiplication by the inverse-transpose matrix. -/
theorem dual_affineAction (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) (w : n → S) :
    ρ.dual.affineAction S x w =
      ((ρ.affineMatrix S x)⁻¹ : GL n S).val.transpose *ᵥ w := by
  rw [affineAction_apply, dual_affineMatrix, GeneralLinear.matrixContragredient_coe]

/-- Evaluation is invariant under the simultaneous dual and original actions. -/
theorem dual_affineAction_pairing (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) (w v : n → S) :
    (ρ.dual.affineAction S x w) ⬝ᵥ (ρ.affineAction S x v) = w ⬝ᵥ v := by
  simp only [affineAction_apply, dual_affineMatrix]
  exact GeneralLinear.matrixContragredient_pairing n (ρ.affineMatrix S x) w v

/-- Under coordinate evaluation, the dual action precomposes with the inverse action. -/
theorem dual_affineAction_evaluation (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ G.X) (w v : n → S) :
    dotProductEquiv S n (ρ.dual.affineAction S x w) v =
      dotProductEquiv S n w (ρ.affineAction S x⁻¹ v) := by
  change (ρ.dual.affineAction S x w) ⬝ᵥ v = w ⬝ᵥ (ρ.affineAction S x⁻¹ v)
  rw [dual_affineAction, affineAction_apply, map_inv]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

/-- Forget invertibility of the affine linear action to obtain Mathlib's representation. -/
def affineRepresentation (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R) :
    Representation S ((algSpec R).obj (op S) ⟶ G.X) (n → S) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ρ.affineAction S)

@[simp] theorem affineRepresentation_apply (ρ : MatrixRepresentation G n)
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ G.X) (v : n → S) :
    ρ.affineRepresentation S x v = ρ.affineAction S x v := rfl

/-- Coordinate evaluation intertwines the dual scheme representation with the full module dual. -/
def affineDualEquiv (ρ : MatrixRepresentation G n) (S : CommAlgCat.{u} R) :
    (ρ.dual.affineRepresentation S).Equiv (ρ.affineRepresentation S).dual where
  toLinearEquiv := dotProductEquiv S n
  isIntertwining' x := by
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro v
    exact dual_affineAction_evaluation ρ S x w v

@[simp] theorem affineDualEquiv_apply (ρ : MatrixRepresentation G n)
    (S : CommAlgCat.{u} R) (w v : n → S) :
    ρ.affineDualEquiv S w v = w ⬝ᵥ v := rfl

/-- Dualizing the trivial coordinate representation leaves it unchanged as a scheme morphism. -/
@[simp] theorem dual_trivial :
    (trivial G n).dual = trivial G n := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv n R T).injective
  change ((trivial G n).dual).pointMatrix T x = (trivial G n).pointMatrix T x
  rw [dual_pointMatrix, trivial_pointMatrix, map_one]

/-- The standard representation dual is exactly the contragredient scheme morphism. -/
@[simp] theorem dual_standard :
    (standard n R).dual = (GeneralLinear.contragredientIso n R).hom :=
  Category.id_comp _

end Langlands.GroupScheme.MatrixRepresentation
