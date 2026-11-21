import Langlands.GroupScheme.CliffordSpin.ScalarIsometryProjection
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeSurjectionProof

/-! # Geometric surjectivity of the scalar Clifford projection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic Langlands.QuadraticForm Langlands.LinearAlgebra.OrthogonalCocycleDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 650000

variable {F : Type u} [Field F] [Invertible (2 : F)] {n : ℕ}
  (Q : QuadraticForm F (Fin n → F))

local notation "b" => Pi.basisFun F (Fin n)

/-- The subgroup in tensor-unit and matrix coordinates is equivalent to the corresponding
Clifford lift group over the coefficient algebra. -/
def coefficientLiftEquiv (A : Type u) [CommRing A] [Algebra F A] :
    coefficientSubgroup Q b A ≃* CliffordSpinLift (Q.baseChange A) where
  toFun x := ⟨pairEquiv Q b A x.val, x.property⟩
  invFun x := ⟨(pairEquiv Q b A).symm x.val, by
    change pairEquiv Q b A ((pairEquiv Q b A).symm x.val) ∈ cliffordSpinLiftSubgroup _
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((pairEquiv Q b A).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((pairEquiv Q b A).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (map_mul (pairEquiv Q b A) x.val y.val)

@[simp] theorem vectorAction_coefficientLiftEquiv (A : Type u) [CommRing A] [Algebra F A]
    (x : coefficientSubgroup Q b A) :
    CliffordSpinLift.vectorAction _ (coefficientLiftEquiv Q A x) = matrixAction b A x.val.2 := rfl

variable [CharZero F] [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "B" => FirstKindInvolution.polar τ q
local notation "Qq" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "P" => groupScheme Qq b

omit [NeZero n] in
/-- The polar matrix remains a regular quadratic form after extending the base field. -/
theorem nondegenerate_polar_baseChange (hq : (τ).IsNondegenerateQuadratic q)
    (K : Type u) [Field K] [Algebra F K] : ((Qq).baseChange K).polarBilin.Nondegenerate := by
  let D := (B).map (algebraMap F K)
  have hD : IsUnit D := hq.map (algebraMap F K).mapMatrix
  have hs : Dᵀ = D := by
    dsimp only [D]
    rw [← Matrix.transpose_map, OrthogonalMatrix.scalar_polar_transpose]
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have h := polar_nondegenerate_of_symmetric_unit hs hD
  let e := gramBaseChangeIsometry (A := K) B
  have hp (v w : K ⊗[F] (Fin n → F)) :
      ((Qq).baseChange K).polarBilin v w = D.toQuadraticForm'.polarBilin (e v) (e w) := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add e,
      QuadraticMap.IsometryEquiv.map_app]
  constructor
  · intro v hv
    apply e.toLinearEquiv.injective
    rw [map_zero]
    apply h.1
    intro w
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective w
    exact (hp v x).symm.trans (hv x)
  · intro w hw
    apply e.toLinearEquiv.injective
    rw [map_zero]
    apply h.2
    intro v
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective v
    exact (hp x w).symm.trans (hw x)

/-- The scalar projection lifts every point over an algebraically closed coefficient field. -/
theorem affinePoints_projection_surjective (hq : (τ).IsNondegenerateQuadratic q)
    (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K] :
    Function.Surjective ((P).affinePointsTarget (projection q) (CommAlgCat.of F K)) := by
  intro y
  let R := CommAlgCat.of F K
  let g := actionMatrix q R y
  have hg := (mem_range_actionMatrix_iff q R g).mp ⟨y, rfl⟩
  let l := matrixAction b K g
  have hl : ∀ v, ((Qq).baseChange K) (l v) = ((Qq).baseChange K) v := hg.1
  let z : ((Qq).baseChange K).IsometryEquiv ((Qq).baseChange K) := ⟨l, hl⟩
  let : Invertible (2 : K) := (Invertible.map (algebraMap F K) 2).copy 2 (map_ofNat _ _).symm
  have hdet : LinearEquiv.det l = 1 := (det_matrixAction b g).trans hg.2
  let : Module.Finite K (K ⊗[F] (Fin n → F)) := Module.Finite.of_basis ((b).baseChange K)
  obtain ⟨c, hc⟩ := exists_cliffordSpinLift_of_isAlgClosed _ (nondegenerate_polar_baseChange q hq K) z hdet
  let x := (affinePairEquiv Qq b R).symm ((coefficientLiftEquiv Qq K).symm c)
  refine ⟨x, (actionMatrix_injective q R) ?_⟩
  change actionMatrix q R (x ≫ (projection q).hom.hom) = g
  rw [actionMatrix_projection, show affinePairEquiv Qq b R x = _ from MulEquiv.apply_symm_apply _ _]
  apply (matrixAction b K).injective
  rw [← vectorAction_coefficientLiftEquiv, MulEquiv.apply_symm_apply, hc]

/-- The underlying projection of schemes is surjective for a regular scalar form. -/
theorem surjective_projection (hq : (τ).IsNondegenerateQuadratic q) :
    Surjective (projection q).hom.hom.left := by
  apply Langlands.AbelianScheme.surjective_of_algClosed_point_lifting
  intro K _ _ s y
  let : Algebra F K := (Spec.preimage s).hom.toAlgebra
  have hs : Spec.algebraMap F K = s := Spec.map_preimage s
  revert y
  rw [← hs]
  exact affinePoints_projection_surjective q hq K

end Langlands.GroupScheme.CliffordSpin
