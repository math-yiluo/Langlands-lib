import Langlands.Algebra.CentralSimple.LandherrEichlerLocal
import Langlands.Algebra.CentralSimple.LandherrNumberFieldNorm
import Langlands.Algebra.NumberFieldReducedNormLocalityProof
import Langlands.ClassFieldTheory.Global.CyclicHasseNormProof
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation
import Langlands.Algebra.ReducedNormScalarExtension

/-! # Reduction of Landherr's theorem to reduced norm one -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open NumberField IsDedekindDomain Filter Topology
open scoped TensorProduct

universe u

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F] in
theorem relNorm_mul (R : Type u) [CommRing R] [Algebra F R] (z z' : R ⊗[F] B) :
    relNorm F E B R (z * z') = relNorm F E B R z * relNorm F E B R z' := by
  simp only [relNorm, map_mul]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F] in
theorem relNorm_one (R : Type u) [CommRing R] [Algebra F R] :
    relNorm F E B R 1 = 1 := by
  simp only [relNorm, map_one]

omit [CharZero F] in
theorem map_qm {R S : Type u} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (φ : R →ₐ[F] S) (p q : R) :
    Algebra.TensorProduct.map (AlgHom.id F E) φ (qm F E R p q) = qm F E S (φ p) (φ q) := by
  simp [qm]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F] in
/-- The relative reduced norm of a unit is a unit. -/
theorem isUnit_relNorm (R : Type u) [CommRing R] [Algebra F R] (x : (R ⊗[F] B)ˣ) :
    IsUnit (relNorm F E B R x) :=
  (x.isUnit.map (UnitaryPoints.tensorEquiv F E B R)).map (reducedNorm E B (E ⊗[F] R))

variable (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

omit [CharZero F] in
/-- `t ⊗ 1` and its conjugate multiply to the image of the quadratic norm. -/
theorem tmul_one_mul_tensorConj (K : Type u) [CommRing K] [Algebra F K] (t : E) :
    (t ⊗ₜ[F] (1 : K)) * tensorConj F E K (t ⊗ₜ[F] (1 : K)) =
      (t * conjugation F E t) ⊗ₜ[F] (1 : K) := by
  rw [tensorConj_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Hilbert 90 normalized by a global element of the same norm. -/
theorem exists_hilbert90_point (K : Type u) [Field K] [Algebra F K] (δ : E ⊗[F] K) (t₀ : E)
    (ht₀ : t₀ ≠ 0)
    (h : δ * tensorConj F E K δ = (t₀ ⊗ₜ[F] (1 : K)) * tensorConj F E K (t₀ ⊗ₜ[F] (1 : K))) :
    ∃ P Q : K, IsUnit (qm F E K P Q) ∧
      δ * tensorConj F E K (qm F E K P Q) = (t₀ ⊗ₜ[F] (1 : K)) * qm F E K P Q := by
  have hσt : conjugation F E t₀ ≠ 0 := by
    intro h0
    exact ht₀ ((conjugation F E).injective (h0.trans (map_zero _).symm))
  set c := δ * (t₀⁻¹ ⊗ₜ[F] (1 : K)) with hc
  have hcc : c * tensorConj F E K c = 1 := by
    rw [hc, map_mul, mul_mul_mul_comm, h, tmul_one_mul_tensorConj, tensorConj_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      map_inv₀]
    rw [show t₀ * conjugation F E t₀ * (t₀⁻¹ * (conjugation F E t₀)⁻¹) = 1 by field_simp]
    rfl
  obtain ⟨P, Q, hu, hω⟩ := exists_hilbert90 F E K c hcc
  refine ⟨P, Q, hu, ?_⟩
  calc δ * tensorConj F E K (qm F E K P Q)
      = (t₀ ⊗ₜ[F] (1 : K)) * (c * tensorConj F E K (qm F E K P Q)) := by
        rw [hc, ← mul_assoc, mul_comm (t₀ ⊗ₜ[F] (1 : K)), mul_assoc δ,
          Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ht₀, mul_one,
          ← Algebra.TensorProduct.one_def, mul_one]
    _ = (t₀ ⊗ₜ[F] (1 : K)) * qm F E K P Q := by rw [← hω]

section NumberField

variable [NumberField F]

include hτ in
/-- Let `τ` act on `E` by quadratic conjugation. If `1 ⊗ y = x τ_R(x)` and the relative
reduced norm of `y` is the scalar `a₀ ∈ F`, then the relative reduced norm of `x` has
quadratic norm equal to the image of `a₀`. -/
theorem relNorm_mul_conj_of_eq (R : Type u) [CommRing R] [Algebra F R] (y : B) (x : R ⊗[F] B)
    (hx : (1 : R) ⊗ₜ[F] y = x * τ.baseChange R x) (a₀ : F)
    (ha : relNorm F E B F ((1 : F) ⊗ₜ[F] y) = qm F E F a₀ 0) :
    relNorm F E B R x * tensorConj F E R (relNorm F E B R x) =
      qm F E R (algebraMap F R a₀) 0 := by
  rw [← relNorm_baseChange F E B τ hτ R x, ← relNorm_mul, ← hx]
  have h := relNorm_naturality F E B (Algebra.ofId F R) ((1 : F) ⊗ₜ[F] y)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, ha, map_qm, map_zero] at h
  exact h

include hτ in
/-- If `τ` acts on `E` by quadratic conjugation, the relative reduced norm of a
`τ`-symmetric element is the image of a scalar in `F`. -/
theorem exists_relNorm_eq_qm (y : B) (hy : τ y = y) :
    ∃ a₀ : F, relNorm F E B F ((1 : F) ⊗ₜ[F] y) = qm F E F a₀ 0 := by
  obtain ⟨p, q, hpq⟩ := exists_eq_qm F E F (relNorm F E B F ((1 : F) ⊗ₜ[F] y))
  have h := relNorm_baseChange F E B τ hτ F ((1 : F) ⊗ₜ[F] y)
  rw [FirstKindInvolution.baseChange_tmul, hy, hpq, tensorConj_qm] at h
  have hq := (qm_injective F E F h).2
  have hq0 : q = 0 := by linear_combination hq / 2
  exact ⟨p, by rw [hpq, hq0]⟩

end NumberField

end Langlands.CentralSimple.Landherr
