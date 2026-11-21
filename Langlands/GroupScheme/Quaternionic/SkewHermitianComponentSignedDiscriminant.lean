import Langlands.GroupScheme.Quaternionic.SkewHermitianLineDiscriminant
import Langlands.GroupScheme.Quaternionic.SkewHermitianOrthogonalBasis
import Langlands.GroupScheme.Quaternionic.MatrixReducedNorm
import Langlands.GroupScheme.Quaternionic.HyperbolicBasis

/-! # Signed discriminant of the rank-three symmetric component -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic FiniteAlgebraUnits.MatrixPoints Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (Q : QuatData F D) (τ : FirstKindInvolution F D) (hbar : ∀ z, τ z = Q.bar z)
  (hτ : ∀ z : D, z * τ z = algebraMap F D (reducedNorm F D F (1 ⊗ₜ[F] z)))

local notation "E" => field Q.c
local notation "V" => Fin 3 → D

omit [CharZero F] [FiniteDimensional F D] [Algebra.IsCentral F D] in
include hbar in
private theorem τ_x : τ Q.x = -Q.x := by
  rw [hbar, ← Q.ι_root, Q.bar_ι, QuadField.conjugation_root, map_neg]

omit [CharZero F] in
include hbar hτ in
private theorem norm_x_eq_neg_root_sq :
    algebraMap F E (reducedNorm F D F (1 ⊗ₜ[F] Q.x)) = -((root : E) ^ 2) := by
  apply Q.ι.injective
  change Q.ι (algebraMap F E (reducedNorm F D F (1 ⊗ₜ[F] Q.x))) = Q.ι (-((root : E) ^ 2))
  rw [Q.ι.commutes, map_neg, map_pow, Q.ι_root, ← hτ, Q.τ_x τ hbar, mul_neg, pow_two]

omit [CharZero F] in
private theorem gramNorm_mul_sq_eq_prod {H : Matrix (Fin 3) (Fin 3) D}
    (hH : τ.IsAntihermitian H) (c : Module.Basis (Fin 3) D V)
    (hc : ∀ i j, i ≠ j → τ.sesqForm H (c i) (c j) = 0)
    (hn : ∀ i, τ.sesqForm H (c i) (c i) ≠ 0) :
    ∃ p : F, p ≠ 0 ∧
      reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) * p ^ 2 =
        ∏ i, reducedNorm F D F (1 ⊗ₜ[F] τ.sesqForm H (c i) (c i)) := by
  let B := AntihermitianForm.ofMatrix hH
  let d : Fin 3 → D := fun i => B (c i) (c i)
  let P : Matrix (Fin 3) (Fin 3) D := Matrix.of c
  have hd : P * H * τ.matrix (Fin 3) P = Matrix.diagonal d := by
    ext i j
    rw [τ.mul_mul_matrix_apply, Matrix.diagonal_apply]
    change B (c i) (c j) = _
    by_cases h : i = j
    · subst j
      rw [ite_eq_left rfl]
    · rw [ite_eq_right h]
      exact hc i j h
  have hdunit : IsUnit (Matrix.diagonal d) :=
    (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (hn i)).map (Matrix.diagonalRingHom (Fin 3) D)
  have hP := τ.isUnit_of_mul_mul_matrix_eq hdunit hd
  let j : D →ₐ[F] F ⊗[F] D := Algebra.TensorProduct.includeRight
  let J := j.mapMatrix (m := Fin 3)
  have hJ (X : Matrix (Fin 3) (Fin 3) D) : J X = coefficientEquiv F D F ((1 : F) ⊗ₜ[F] X) := by
    ext i k
    rw [coefficientEquiv_tmul]
    rfl
  have hJadj : J (τ.matrix (Fin 3) P) = (τ.baseChange F).matrix (Fin 3) (J P) := by
    ext i k
    rw [hJ, hJ, FirstKindInvolution.matrix_apply, coefficientEquiv_tmul, coefficientEquiv_tmul,
      FirstKindInvolution.matrix_apply, FirstKindInvolution.baseChange_tmul]
  have hJdiag : J (Matrix.diagonal d) = Matrix.diagonal (fun i => (1 : F) ⊗ₜ[F] d i) :=
    Matrix.diagonal_map (map_zero j)
  have hprod : matrixReducedNorm F (J H) * (matrixReducedNorm F (J P)) ^ 2 =
      ∏ i, reducedNorm F D F (1 ⊗ₜ[F] d i) := by
    rw [← matrixReducedNorm_congruence F τ, ← hJadj, ← map_mul, ← map_mul, hd, hJdiag,
      matrixReducedNorm_diagonal]
  have hNH : matrixReducedNorm F (J H) = reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) := by
    rw [hJ]
    change reducedNorm F (Matrix (Fin 3) (Fin 3) D) F
      ((coefficientEquiv F D F).symm (coefficientEquiv F D F ((1 : F) ⊗ₜ[F] H))) = _
    rw [AlgEquiv.symm_apply_apply]
  exact ⟨matrixReducedNorm F (J P), ((hP.map J).map (matrixReducedNorm F)).ne_zero, hNH ▸ hprod⟩

include hτ in
/-- If the distinguished pure quaternion has the rank-three Gram norm, the
  determinant of the symmetric component in a suitable basis is negative a square. -/
theorem exists_component_basis_det_eq_neg_sq {H : Matrix (Fin 3) (Fin 3) D}
    (hH : τ.IsAntihermitian H) (hu : IsUnit H)
    (hN : reducedNorm F D F (1 ⊗ₜ[F] Q.x) = reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H)) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∃ (b : Module.Basis (Fin 2 × Fin 3) E V) (s : E),
      s ≠ 0 ∧
        (LinearMap.toMatrix₂ b b (Q.symmetricComponent (AntihermitianForm.ofMatrix hH) hbar)).det = -(s ^ 2) := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let B := AntihermitianForm.ofMatrix hH
  have hx0 := Q.basis.ne_zero 1
  rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1] at hx0
  have hne : ∃ a, τ a ≠ a := by
    refine ⟨Q.x, fun h => smul_ne_zero (two_ne_zero : (2 : F) ≠ 0) hx0 ?_⟩
    rw [two_smul]
    exact (congrArg (fun z : D => z + Q.x) (h.symm.trans (Q.τ_x τ hbar))).trans (neg_add_cancel _)
  have hr : Module.finrank D V = 3 := Module.finrank_fin_fun D
  obtain ⟨c₀, hc₀, hn₀⟩ := AntihermitianForm.orthogonalBasis F D τ V B hne
    (AntihermitianForm.ofMatrix_separatingLeft hH hu)
  let e := finCongr hr
  let c := c₀.reindex e
  have hc (i j : Fin 3) (h : i ≠ j) : B (c i) (c j) = 0 := by
    simp only [c, Module.Basis.reindex_apply]
    exact hc₀ _ _ (fun he => h (e.symm.injective he))
  have hn (i : Fin 3) : B (c i) (c i) ≠ 0 := by
    simp only [c, Module.Basis.reindex_apply]
    exact hn₀ _
  obtain ⟨p, hnp, hp⟩ := gramNorm_mul_sq_eq_prod τ hH c hc hn
  have hnRoot : (root : E) ≠ 0 := fun hz => hx0 (by rw [← Q.ι_root, hz, map_zero])
  have hnPE : algebraMap F E p ≠ 0 := by
    simpa only [map_zero] using (algebraMap F E).injective.ne hnp
  refine ⟨Q.componentBasis c, (root : E) * algebraMap F E p,
    mul_ne_zero hnRoot hnPE, ?_⟩
  rw [Q.det_componentBasis_eq_prod_reducedNorm B hbar hτ c hc]
  change algebraMap F E (∏ i, reducedNorm F D F (1 ⊗ₜ[F] τ.sesqForm H (c i) (c i))) = _
  rw [← hp, ← hN, map_mul, map_pow, Q.norm_x_eq_neg_root_sq τ hbar hτ]
  ring

/-- A norm representative of the Gram discriminant makes the symmetric component's
  discriminant the negative of a nonzero square over the corresponding quadratic field. -/
def ComponentSignedDiscriminantStatement : Prop :=
  ∀ (F D : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D]
    (Q : QuatData F D) (τ : FirstKindInvolution F D) (hbar : ∀ z, τ z = Q.bar z),
    (∀ z : D, z * τ z = algebraMap F D (reducedNorm F D F (1 ⊗ₜ[F] z))) →
    ∀ (H : Matrix (Fin 3) (Fin 3) D) (hH : τ.IsAntihermitian H), IsUnit H →
    reducedNorm F D F (1 ⊗ₜ[F] Q.x) = reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) →
    let K := field Q.c
    let U := Fin 3 → D
    letI : Module K U := Module.compHom U Q.ι.toRingHom
    ∃ (b : Module.Basis (Fin 2 × Fin 3) K U) (s : K),
      s ≠ 0 ∧
        (LinearMap.toMatrix₂ b b (Q.symmetricComponent (AntihermitianForm.ofMatrix hH) hbar)).det = -(s ^ 2)

theorem componentSignedDiscriminant : ComponentSignedDiscriminantStatement.{u} := by
  intro F D _ _ _ _ _ _ Q τ hbar hτ H hH hu hn
  exact Q.exists_component_basis_det_eq_neg_sq τ hbar hτ hH hu hn

end Langlands.GroupScheme.KneserThree.QuatData
