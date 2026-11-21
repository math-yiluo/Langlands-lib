import Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion
import Langlands.GroupScheme.SymplecticInnerForm.AlgebraTransport
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction

/-! # Quaternionic spin presentations in skew-hermitian coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] (σ : FirstKindInvolution F D)
  {I : Type} [Fintype I] [DecidableEq I]
  (q : σ.QuadraticForms I)

omit [CharZero F] [FiniteDimensional F D] in
private theorem polar_eq_out_add : σ.polar q = Quotient.out q + σ.matrix I (Quotient.out q) := by
  have h := σ.polar_mk (Quotient.out q)
  rw [Submodule.Quotient.mk_out] at h
  exact h

private theorem range_isometryGroupι_iff_polar {T : Over (Spec (CommRingCat.of F))}
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis F (Matrix I I D))).X) :
    x ∈ (SubgroupFunctor.range (σ.isometryGroupι q)).carrier T ↔
      x ∈ (SubgroupFunctor.range (σ.unitaryGroupι (σ.polar q))).carrier T := by
  let R := ((algΓ (CommRingCat.of F)).obj T).unop
  let Θ := (σ.matrix I).baseChange R
  let Q : Matrix I I D := Quotient.out q
  let y := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis F (Matrix I I D)) T x :
    R ⊗[F] Matrix I I D)
  rw [σ.mem_range_isometryGroupι_iff q Q (Submodule.Quotient.mk_out q),
    σ.mem_range_unitaryGroupι_iff]
  change IsometryCut.defect (σ.matrix I) Q y ∈ ((σ.matrix I).alternatingSubspace).baseChange R ↔
    y * ((1 : R) ⊗ₜ[F] σ.polar q) * Θ y = (1 : R) ⊗ₜ[F] σ.polar q
  rw [IsometryCut.alternatingSubspace_baseChange,
    Submodule.restrictScalars_mem, σ.polar_eq_out_add, TensorProduct.tmul_add]
  change IsometryCut.defect (σ.matrix I) Q y ∈ Θ.alternatingSubspace ↔
    y * ((1 : R) ⊗ₜ[F] Q + (1 : R) ⊗ₜ[F] σ.matrix I Q) * Θ y =
      (1 : R) ⊗ₜ[F] Q + (1 : R) ⊗ₜ[F] σ.matrix I Q
  have hpol : Θ ((1 : R) ⊗ₜ[F] Q) = (1 : R) ⊗ₜ[F] σ.matrix I Q :=
    (σ.matrix I).baseChange_tmul (1 : R) Q
  rw [← hpol]
  constructor
  · intro hy
    have h : IsometryCut.defect (σ.matrix I) Q y +
        Θ (IsometryCut.defect (σ.matrix I) Q y) = 0 := by
      obtain ⟨a, ha⟩ := Θ.mem_alternatingSubspace.1 hy
      rw [← ha, Θ.map_sub, Θ.apply_apply]
      abel
    change (y * ((1 : R) ⊗ₜ[F] Q) * Θ y - (1 : R) ⊗ₜ[F] Q) +
      Θ (y * ((1 : R) ⊗ₜ[F] Q) * Θ y - (1 : R) ⊗ₜ[F] Q) = 0 at h
    rw [Θ.map_sub, Θ.map_mul, Θ.map_mul, Θ.apply_apply] at h
    apply sub_eq_zero.mp
    rw [mul_add, add_mul]
    rw [← h]
    noncomm_ring
  · intro h
    have hh : (2 : R) * algebraMap F R ((2 : F)⁻¹) = 1 := by
      rw [← _root_.map_ofNat (algebraMap F R) 2, ← _root_.map_mul, mul_inv_cancel₀ two_ne_zero, _root_.map_one]
    exact KneserThree.defect_mem_of_polar Θ hh h

variable [Algebra.IsCentral F D] (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

local notation "τ" => σ.quaternionConjugation hdim hsym
local notation "l" => (σ.quaternionAlternatingUnit hdim hsym : D)

private def rightMultiplier : Matrix I I D := Matrix.scalar I l⁻¹

/-- The skew-hermitian Gram matrix for standard conjugation coming from the quadratic
  form with the original orthogonal involution. -/
def conjugationSkewGram : Matrix I I D := σ.polar q * σ.rightMultiplier hdim hsym

omit [CharZero F] [Algebra.IsCentral F D] in
private theorem isUnit_rightMultiplier : IsUnit (σ.rightMultiplier (I := I) hdim hsym) :=
  (isUnit_iff_ne_zero.mpr (inv_ne_zero (σ.quaternionAlternatingUnit hdim hsym).ne_zero)).map
    (Matrix.scalar I)

omit [CharZero F] [Algebra.IsCentral F D] in
private theorem conjugation_matrix_intertwine (A : Matrix I I D) :
    (σ.matrix I) A * σ.rightMultiplier hdim hsym =
      σ.rightMultiplier hdim hsym * ((τ).matrix I) A := by
  ext i j
  simp only [rightMultiplier, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    FirstKindInvolution.matrix_apply]
  change σ (A j i) * l⁻¹ = l⁻¹ * (l * σ (A j i) * l⁻¹)
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (σ.quaternionAlternatingUnit hdim hsym).ne_zero, one_mul]

omit [CharZero F] [Algebra.IsCentral F D] in
private theorem conjugation_matrix_rightMultiplier :
    ((τ).matrix I) (σ.rightMultiplier (I := I) hdim hsym) = -(σ.rightMultiplier hdim hsym) := by
  have hl : τ l⁻¹ = -l⁻¹ := by
    rw [(τ).map_inv, KneserThree.Quaternion.conj_ell σ hdim hsym, inv_neg]
  ext i j
  by_cases h : i = j
  · subst j
    simpa only [rightMultiplier, Matrix.scalar_apply, FirstKindInvolution.matrix_apply,
      Matrix.neg_apply, Matrix.diagonal_apply_eq] using hl
  · simp [rightMultiplier, Matrix.scalar_apply, FirstKindInvolution.matrix_apply, h, Ne.symm h]

omit [Algebra.IsCentral F D] in
/-- The twisted polar matrix is skew-hermitian for the canonical quaternion conjugation. -/
theorem isAntihermitian_conjugationSkewGram : (τ).IsAntihermitian (σ.conjugationSkewGram q hdim hsym) := by
  have hp : (σ.matrix I) (σ.polar q) = σ.polar q := by
    rw [σ.polar_eq_out_add, FirstKindInvolution.map_add, FirstKindInvolution.apply_apply, add_comm]
  have h := σ.conjugation_matrix_intertwine hdim hsym (σ.polar q)
  rw [hp] at h
  have hskew : ((τ).matrix I) (σ.conjugationSkewGram q hdim hsym) = -(σ.conjugationSkewGram q hdim hsym) := by
    rw [conjugationSkewGram, FirstKindInvolution.map_mul, σ.conjugation_matrix_rightMultiplier hdim hsym,
      neg_mul, ← h]
  refine ⟨hskew, fun i => ?_⟩
  apply KneserThree.mem_alternatingSubspace_of_neg τ (h := (2 : F)⁻¹) (mul_inv_cancel₀ two_ne_zero)
  exact congrArg (fun M : Matrix I I D => M i i) hskew

omit [CharZero F] [Algebra.IsCentral F D] in
/-- Nondegeneracy is preserved by the invertible quaternionic Gram multiplier. -/
theorem isUnit_conjugationSkewGram (hq : σ.IsNondegenerateQuadratic q) :
    IsUnit (σ.conjugationSkewGram q hdim hsym) := hq.mul (σ.isUnit_rightMultiplier hdim hsym)

/-- The full isometry group scheme is the unitary group of the skew-hermitian Gram matrix. -/
def conjugationSkewIsometryIso : σ.isometryGroup q ≅ (τ).unitaryGroup (σ.conjugationSkewGram q hdim hsym) := by
  apply (σ.isClosedSubgroup_isometryGroupι q).sourceIsoOfRangeEq
    ((τ).isClosedSubgroup_unitaryGroupι (σ.conjugationSkewGram q hdim hsym))
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [σ.range_isometryGroupι_iff_polar q, σ.mem_range_unitaryGroupι_iff, (τ).mem_range_unitaryGroupι_iff]
  let R := ((algΓ (CommRingCat.of F)).obj T).unop
  let A := Matrix I I D
  let H := σ.polar q
  let Λ := σ.rightMultiplier (I := I) hdim hsym
  let y := (FiniteAlgebraUnits.pointsEquiv (Module.finBasis F A) T x : R ⊗[F] A)
  have hΛ : IsUnit ((1 : R) ⊗ₜ[F] Λ) :=
    (σ.isUnit_rightMultiplier hdim hsym).map (Algebra.TensorProduct.includeRight : A →ₐ[F] R ⊗[F] A)
  have h := SymplecticInnerForm.tensor_adjoint_compatibility (σ.matrix I) ((τ).matrix I)
    (AlgEquiv.refl : A ≃ₐ[F] A) Λ (σ.conjugation_matrix_intertwine hdim hsym) R y
  have he : (σ.matrix I).baseChange R y * ((1 : R) ⊗ₜ[F] Λ) =
      ((1 : R) ⊗ₜ[F] Λ) * ((τ).matrix I).baseChange R y := by
    simpa only [AlgEquiv.refl_toAlgHom, Algebra.TensorProduct.map_id, AlgHom.id_apply] using h
  change y * ((1 : R) ⊗ₜ[F] H) * (σ.matrix I).baseChange R y = ((1 : R) ⊗ₜ[F] H) ↔
    y * ((1 : R) ⊗ₜ[F] (H * Λ)) * ((τ).matrix I).baseChange R y = ((1 : R) ⊗ₜ[F] (H * Λ))
  have hmul : ((1 : R) ⊗ₜ[F] (H * Λ)) = ((1 : R) ⊗ₜ[F] H) * ((1 : R) ⊗ₜ[F] Λ) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hmul, ← mul_assoc y, mul_assoc (y * ((1 : R) ⊗ₜ[F] H)), ← he,
    ← mul_assoc (y * ((1 : R) ⊗ₜ[F] H)), hΛ.mul_left_inj]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
