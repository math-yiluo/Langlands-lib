import Langlands.GroupScheme.OddOrthogonalMatrix.Representation
import Langlands.GroupScheme.OrthogonalMatrix.Torus

/-! # The diagonal torus and its odd standard representation weights -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

/-- The odd standard weights are `1,t_a,t_a⁻¹`. -/
def torusWeights {A : Type*} [CommRing A] (τ : ULift.{u} l → Aˣ) : Index l → Aˣ :=
  Sum.elim (fun _ => 1) (SymplecticMatrix.torusWeights τ)

/-- Integral coordinates of the weights `0,e_a,-e_a`. -/
def weightCoord (l : Type) [DecidableEq l] : Index l → l → ℤ :=
  Sum.elim (fun _ => 0) (SymplecticMatrix.weightCoord l)

omit [Fintype l] in
@[simp] theorem weightCoord_axis : weightCoord l (Sum.inl ()) = 0 := rfl

omit [Fintype l] in
@[simp] theorem weightCoord_signed (a : l ⊕ l) :
    weightCoord l (Sum.inr a) = SymplecticMatrix.weightCoord l a := rfl

theorem torusWeights_eq_prod {A : Type*} [CommRing A] (τ : ULift.{u} l → Aˣ) (x : Index l) :
    torusWeights τ x = ∏ c : ULift.{u} l, τ c ^ weightCoord l x c.down := by
  cases x with
  | inl a => simp [torusWeights, weightCoord]
  | inr a => exact SymplecticMatrix.torusWeights_eq_prod τ a

theorem prod_zpow_weightCoord_sub {A : Type*} [CommRing A]
    (τ : ULift.{u} l → Aˣ) (x y : Index l) :
    ∏ c : ULift.{u} l, τ c ^ (weightCoord l x - weightCoord l y) c.down =
      torusWeights τ x * (torusWeights τ y)⁻¹ := by
  rw [torusWeights_eq_prod, torusWeights_eq_prod, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun c _ => by rw [Pi.sub_apply, zpow_sub])

theorem torusWeights_mulSingle {A : Type*} [CommRing A]
    (c : ULift.{u} l) (U : Aˣ) (x : Index l) :
    torusWeights (Pi.mulSingle c U) x = U ^ weightCoord l x c.down := by
  rw [torusWeights_eq_prod]
  exact GeneralLinear.prod_mulSingle_zpow (n := l) c U _

theorem det_evenTorusWeights {A : Type*} [CommRing A] (τ : ULift.{u} l → Aˣ) :
    (Matrix.diagonal (fun a : l ⊕ l => (SymplecticMatrix.torusWeights τ a : A))).det = 1 := by
  rw [Matrix.det_diagonal, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro a _
  change (τ ⟨a⟩ : A) * ((τ ⟨a⟩)⁻¹ : Aˣ) = 1
  exact congrArg (fun v : Aˣ => (v : A)) (mul_inv_cancel (τ ⟨a⟩))

variable (l) (K : Type u) [Field K]

/-- The actual diagonal split torus, embedded through the determinant-corrected
even inclusion. Its axis coordinate is always one. -/
def diagonalTorus :
    (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} l)).toGrp ⟶
      groupScheme l K :=
  OrthogonalMatrix.diagonalTorus l (CommRingCat.of K) ≫ evenMap K

instance mono_diagonalTorus : Mono (diagonalTorus l K).hom.hom := by
  change Mono ((OrthogonalMatrix.diagonalTorus l (CommRingCat.of K)).hom.hom ≫
    (evenMap K).hom.hom)
  infer_instance

/-- The actual diagonal torus is a closed split subtorus of the odd group. -/
theorem isSplitSubtorus_diagonalTorus : IsSplitSubtorus (diagonalTorus l K) :=
  ⟨SymplecticMatrix.isSplitTorus_diagonalTorus l K,
    IsTorus.isClosedSubgroup_of_mono
      (IsSplitTorus.isTorus (SymplecticMatrix.isSplitTorus_diagonalTorus l K)) _⟩

variable {l K}

/-- The actual diagonal torus has precisely its standard odd diagonal weights
over every affine coefficient algebra. -/
theorem affinePointsEquiv_diagonalTorus_inclusion {A : Type u} [CommRing A] [Algebra K A]
    (t : Lie.AffinePoints
      (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} l)).toGrp A) :
    GeneralLinear.affinePointsEquiv (Index l) (CommRingCat.of K)
      (CommAlgCat.of (CommRingCat.of K) A) (t ≫ (diagonalTorus l K ≫ inclusion K).hom.hom) =
      GeneralLinear.diagonalTorusUnits (Index l) A
        (fun c : ULift.{u} (Index l) => torusWeights (GeneralLinear.torusCoords t) c.down) := by
  rw [Grp.comp_hom_hom, ← Category.assoc, affinePointsEquiv_inclusion]
  rw [diagonalTorus, Grp.comp_hom_hom, ← Category.assoc, affineMatrix_evenMap]
  have h := OrthogonalMatrix.affinePointsEquiv_diagonalTorus_inclusion t
  rw [Grp.comp_hom_hom, ← Category.assoc, OrthogonalMatrix.affinePointsEquiv_inclusion] at h
  have hm := congrArg Units.val h
  change (OrthogonalMatrix.affinePointsEquiv l (CommRingCat.of K)
    (CommAlgCat.of (CommRingCat.of K) A)
      (t ≫ (OrthogonalMatrix.diagonalTorus l (CommRingCat.of K)).hom.hom) :
        Matrix (l ⊕ l) (l ⊕ l) A) =
      Matrix.diagonal (fun a => (SymplecticMatrix.torusWeights (GeneralLinear.torusCoords t) a : A)) at hm
  apply Units.ext
  change evenBlock _ = _
  unfold evenBlock
  erw [hm, det_evenTorusWeights]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GeneralLinear.coe_diagonalTorusUnits, Matrix.diagonal_apply, torusWeights]

open GeneralLinear.DualNumber

local notation "𝔗" => splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift l)

/-- Reconstructing the linear differential recovers the actual tangent image. -/
theorem pointKernelLinearEquiv_lieMatrix
    (X : Additive (lieKernel (groupScheme l K) K)) :
    pointKernelLinearEquiv (lieMatrix K X) = Lie.targetMapLinear (inclusion K) K X :=
  LinearEquiv.apply_symm_apply _ _

/-- Membership in an actual torus weight space in the standard matrix coordinates. -/
theorem mem_weightSpace_diagonalTorus_iff
    (X : Additive (lieKernel (groupScheme l K) K)) (χ : characterLattice 𝔗) :
    X ∈ weightSpace (diagonalTorus l K) χ ↔
      ∀ (A : Type u) [CommRing A] [Algebra K A] (t : Lie.AffinePoints (𝔗).toGrp A)
        (x y : Index l),
        (torusWeights (GeneralLinear.torusCoords t) x : A) * algebraMap K A (lieMatrix K X x y) *
            (((torusWeights (GeneralLinear.torusCoords t) y)⁻¹ : Aˣ) : A) =
          (Lie.characterValue χ t : A) * algebraMap K A (lieMatrix K X x y) := by
  rw [← lieKernelHomLinear_mem_weightSpace_iff (inclusion K),
    ← pointKernelLinearEquiv_lieMatrix, mem_weightSpace]
  refine forall_congr' fun A => ?_
  refine ⟨fun h _ _ t a b => ?_, fun h _ _ t => ?_⟩
  · have h1 := h t
    rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      EmbeddingLike.apply_eq_iff_eq, affinePointsEquiv_diagonalTorus_inclusion] at h1
    have h2 := congrFun (congrFun h1 a) b
    simpa only [GeneralLinear.coe_diagonalTorusUnits, SymplecticMatrix.coe_inv_diagonalTorusUnits,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h2
  · rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      affinePointsEquiv_diagonalTorus_inclusion]
    congr 1
    ext a b
    simpa only [GeneralLinear.coe_diagonalTorusUnits, SymplecticMatrix.coe_inv_diagonalTorusUnits,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h t a b

/-- The actual torus weight is determined by every nonzero matrix entry,
as an integral character equality rather than equality modulo the characteristic. -/
theorem mem_weightSpace_diagonalTorus_iff_support
    (X : Additive (lieKernel (groupScheme l K) K)) (χ : characterLattice 𝔗) :
    X ∈ weightSpace (diagonalTorus l K) χ ↔
      ∀ x y : Index l, lieMatrix K X x y ≠ 0 →
        GeneralLinear.characterCoordEquiv l K χ = weightCoord l x - weightCoord l y := by
  rw [mem_weightSpace_diagonalTorus_iff]
  constructor
  · intro hX x y hxy
    funext c
    have h1 := hX K[T;T⁻¹] (GeneralLinear.affineTorusPoint (R := CommRingCat.of K)
      (Pi.mulSingle ⟨c⟩ (Gm.relativeCoordUnit K))) x y
    rw [SymplecticMatrix.characterValue_eq_prod, GeneralLinear.torusCoords_affineTorusPoint,
      GeneralLinear.prod_mulSingle_zpow, torusWeights_mulSingle, torusWeights_mulSingle,
      ← zpow_neg, Gm.relativeCoordUnit_zpow_val, Gm.relativeCoordUnit_zpow_val,
      Gm.relativeCoordUnit_zpow_val, ← LaurentPolynomial.C_eq_algebraMap] at h1
    refine (GeneralLinear.exponent_eq_of_C_mul_T hxy ?_).symm
    have h1' : LaurentPolynomial.T (weightCoord l x c) * LaurentPolynomial.C (lieMatrix K X x y) *
        LaurentPolynomial.T (-weightCoord l y c) =
        LaurentPolynomial.T (GeneralLinear.characterCoordEquiv l K χ c) *
          LaurentPolynomial.C (lieMatrix K X x y) := h1
    rw [Pi.sub_apply, sub_eq_add_neg, LaurentPolynomial.T_add]
    linear_combination -h1'
  · intro hsupp A _ _ t x y
    by_cases hxy : lieMatrix K X x y = 0
    · rw [hxy, map_zero, mul_zero, zero_mul, mul_zero]
    · have hχ := SymplecticMatrix.characterValue_eq_prod χ t
      rw [hsupp x y hxy, prod_zpow_weightCoord_sub] at hχ
      rw [hχ, Units.val_mul]
      ring

end Langlands.GroupScheme.OddOrthogonalMatrix
