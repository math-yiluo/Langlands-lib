import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoClassGroup
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicBundleMumfordProof
import Mathlib.Algebra.Polynomial.Roots

/-! # Extending the `k^(2g)` Euler scaling from `k` invertible in the base field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The `k^(2g)` scaling of `AlgClosedFieldAmpleEulerInverseScalingStatement`, restricted to
those `k ≥ 1` whose image `(k : K)` in the base field is nonzero. -/
def AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (g : ℕ),
    A.HasRelativeDimension g →
      ∀ (H N : LineBundle A.X.left), H.IsAmple →
        Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left) →
          ∀ (k : ℕ), 1 ≤ k → (k : K) ≠ 0 →
            ∀ (Nk : LineBundle A.X.left),
              Nonempty (tensorObj (tensorPow H.obj k) Nk.obj ≅ structureSheaf A.X.left) →
                ∀ (hH : HasFiniteCohomology A.X.hom H.obj)
                  (hN : HasFiniteCohomology A.X.hom N.obj)
                  (hHk : HasFiniteCohomology A.X.hom (tensorPow H.obj k))
                  (hNk : HasFiniteCohomology A.X.hom Nk.obj),
                  eulerCharacteristic A.X.hom (tensorPow H.obj k) hHk *
                      eulerCharacteristic A.X.hom Nk.obj hNk =
                    (k : ℤ) ^ (2 * g) *
                      (eulerCharacteristic A.X.hom H.obj hH *
                        eulerCharacteristic A.X.hom N.obj hN)

/-- The isomorphism class of a line bundle, for the proved tensor preservation. -/
local notation "cls" => LineBundle.isoClass pullbackTensorComparisonIsIso

section Classes

variable {X : Scheme.{u}}

/-- Actual tensor powers of a line bundle have the powers of its class: the published
`isoClass_tensorPow` for the proved tensor preservation. -/
lemma isoClass_tensorPow_eq_pow (L : LineBundle X) (k : ℕ) :
    cls (⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne X L k⟩ : LineBundle X) =
      cls L ^ k :=
  isoClass_tensorPow pullbackTensorComparisonIsIso L k

/-- A tensor inverse of a line bundle has the inverse class. -/
lemma isoClass_eq_inv_of_tensorObj_iso (L M : LineBundle X)
    (e : tensorObj L.obj M.obj ≅ structureSheaf X) : cls M = (cls L)⁻¹ := by
  have h := LineBundle.isoClass_eq_of_iso (preservation := pullbackTensorComparisonIsIso)
    (ObjectProperty.isoMk _ e :
      LineBundle.tensor pullbackTensorComparisonIsIso L M ≅ LineBundle.trivial X)
  rw [LineBundle.isoClass_tensor, LineBundle.isoClass_trivial] at h
  exact eq_inv_of_mul_eq_one_right h

/-- If `M` is a tensor inverse of `L`, then `M^{⊗k}` is a tensor inverse of `L^{⊗k}`. -/
lemma nonempty_tensorPow_tensorObj_tensorPow_iso (L M : LineBundle X)
    (e : tensorObj L.obj M.obj ≅ structureSheaf X) (k : ℕ) :
    Nonempty (tensorObj (tensorPow L.obj k) (tensorPow M.obj k) ≅ structureSheaf X) := by
  have h : cls (LineBundle.tensor pullbackTensorComparisonIsIso
      ⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne X L k⟩
      ⟨tensorPow M.obj k, tensorPow_isLocallyFreeRankOne X M k⟩) =
        cls (LineBundle.trivial X) := by
    rw [LineBundle.isoClass_tensor, isoClass_tensorPow_eq_pow, isoClass_tensorPow_eq_pow,
      isoClass_eq_inv_of_tensorObj_iso L M e, inv_pow, mul_inv_cancel,
      LineBundle.isoClass_trivial]
  obtain ⟨f⟩ := LineBundle.isoClass_eq_iff.mp h
  exact ⟨(LineBundle.forget X).mapIso f⟩

/-- Any tensor inverse of `L^{⊗k}` is isomorphic to `M^{⊗k}`, for `M` a tensor inverse
of `L`. -/
lemma nonempty_iso_tensorPow_of_inverse (L M Mk : LineBundle X)
    (e : tensorObj L.obj M.obj ≅ structureSheaf X) (k : ℕ)
    (ek : tensorObj (tensorPow L.obj k) Mk.obj ≅ structureSheaf X) :
    Nonempty (Mk.obj ≅ tensorPow M.obj k) := by
  have h : cls Mk = cls (⟨tensorPow M.obj k, tensorPow_isLocallyFreeRankOne X M k⟩ :
      LineBundle X) := by
    rw [isoClass_eq_inv_of_tensorObj_iso
        ⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne X L k⟩ Mk ek, isoClass_tensorPow_eq_pow,
      isoClass_tensorPow_eq_pow, isoClass_eq_inv_of_tensorObj_iso L M e, inv_pow]
  obtain ⟨f⟩ := LineBundle.isoClass_eq_iff.mp h
  exact ⟨(LineBundle.forget X).mapIso f⟩

end Classes

/-- Every rational number is exceeded by a positive integer which is nonzero in a given field:
of two consecutive integers, at least one is nonzero in the field. -/
lemma exists_nat_cast_ne_zero_gt (K : Type u) [Field K] (a : ℚ) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : K) ≠ 0 ∧ a < n := by
  have hm : a ≤ (⌈a⌉₊ : ℚ) := Nat.le_ceil a
  by_cases h1 : ((⌈a⌉₊ + 1 : ℕ) : K) = 0
  · refine ⟨⌈a⌉₊ + 2, by omega, ?_, ?_⟩
    · have h2 : ((⌈a⌉₊ + 2 : ℕ) : K) = ((⌈a⌉₊ + 1 : ℕ) : K) + 1 := by
        push_cast
        ring
      rw [h2, h1, zero_add]
      exact one_ne_zero
    · push_cast
      linarith
  · exact ⟨⌈a⌉₊ + 1, by omega, h1, by push_cast; linarith⟩

/-- The `k^(2g)` scaling for `k` invertible in the base field implies it for every `k ≥ 1`.
Both sides are polynomial in `k`: the Euler characteristics of `H^{⊗k}` and of the inverse
`N^{⊗k}` are values of rational Euler polynomials. Their product agrees with
`χ(H) χ(N) X^(2g)` at the infinitely many positive integers invertible in the field, so
the two polynomials are equal. -/
theorem algClosedFieldAmpleEulerInverseScaling_of_coprime :
    AlgClosedFieldAmpleEulerInverseScalingCoprimeStatement.{u} →
      AlgClosedFieldAmpleEulerInverseScalingStatement.{u} := by
  intro hcop K _ _ A g hg H N hH ⟨eHN⟩ k hk Nk ⟨eNk⟩ hHfin hNfin hHk hNk
  obtain ⟨hHpow, PH, hPH, -⟩ := smoothProperLineBundleEulerPolynomial_degree_le A.X.hom g hg H
  obtain ⟨hNpow, PN, hPN, -⟩ := smoothProperLineBundleEulerPolynomial_degree_le A.X.hom g hg N
  set c : ℤ := eulerCharacteristic A.X.hom H.obj hHfin *
    eulerCharacteristic A.X.hom N.obj hNfin with hc
  have hval : ∀ n : ℕ, 1 ≤ n → (n : K) ≠ 0 →
      (PH * PN).eval (n : ℚ) =
        (Polynomial.X ^ (2 * g) * Polynomial.C (c : ℚ)).eval (n : ℚ) := by
    intro n hn hnK
    have h := hcop K A g hg H N hH ⟨eHN⟩ n hn hnK
      ⟨tensorPow N.obj n, tensorPow_isLocallyFreeRankOne _ N n⟩
      (nonempty_tensorPow_tensorObj_tensorPow_iso H N eHN n) hHfin hNfin (hHpow n) (hNpow n)
    rw [← hc] at h
    rw [Polynomial.eval_mul, hPH, hPN, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact_mod_cast h
  have hpoly : PH * PN = Polynomial.X ^ (2 * g) * Polynomial.C (c : ℚ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hnK, han⟩ := exists_nat_cast_ne_zero_gt K a
    exact ⟨n, hval n hn hnK, han⟩
  obtain ⟨f⟩ := nonempty_iso_tensorPow_of_inverse H N Nk eHN k eNk
  have hNk' : eulerCharacteristic A.X.hom Nk.obj hNk =
      eulerCharacteristic A.X.hom (tensorPow N.obj k) (hNpow k) :=
    eulerCharacteristic_eq_of_iso A.X.hom hNk (hNpow k) f
  have hk' := congrArg (Polynomial.eval (k : ℚ)) hpoly
  rw [Polynomial.eval_mul, hPH, hPN, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hk'
  rw [hNk']
  exact_mod_cast hk'

end Langlands.AbelianScheme
