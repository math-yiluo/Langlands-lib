import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Whittaker.GeneralLinear
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Whittaker pairing normalization

The integral equation in Shahidi's Lemma 1.1, using an actual invariant positive
form and the standard upper-unipotent character. The source pairing is linear
in its first argument, so the arguments of `InvariantPositiveForm.inner` are
reversed. This relation includes integrability and asserts no existence.
-/

noncomputable section

namespace Langlands.Shahidi

open MeasureTheory GeneralLinear Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F) (n : ℕ)
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
variable (b : InvariantPositiveForm π)

/-- The source kernel `⟨v, π(u) w⟩ χ(u)`, with its Hermitian convention made
explicit and with the actual upper-unipotent action. -/
def whittakerPairingIntegrand (v w : V) (u : upperUnipotent (n + 1) F) : ℂ :=
  b.inner (π u.val w) v * (standardCharacter ψ n u : ℂ)

@[simp] theorem whittakerPairingIntegrand_one (v w : V) :
    whittakerPairingIntegrand ψ n π b v w 1 = b.inner w v := by
  simp [whittakerPairingIntegrand]

theorem whittakerPairingIntegrand_smul_left (c : ℂ) (v w : V)
    (u : upperUnipotent (n + 1) F) :
    whittakerPairingIntegrand ψ n π b (c • v) w u =
      c * whittakerPairingIntegrand ψ n π b v w u := by
  unfold whittakerPairingIntegrand
  rw [← b.conj_inner_symm, b.smul_left, map_mul]
  simp only [starRingEnd_self_apply, b.conj_inner_symm]
  ring

theorem whittakerPairingIntegrand_smul_right (c : ℂ) (v w : V)
    (u : upperUnipotent (n + 1) F) :
    whittakerPairingIntegrand ψ n π b v (c • w) u =
      starRingEnd ℂ c * whittakerPairingIntegrand ψ n π b v w u := by
  unfold whittakerPairingIntegrand
  rw [map_smul, b.smul_left, mul_assoc]

theorem whittakerPairingIntegrand_add_left (v v' w : V)
    (u : upperUnipotent (n + 1) F) :
    whittakerPairingIntegrand ψ n π b (v + v') w u =
      whittakerPairingIntegrand ψ n π b v w u +
        whittakerPairingIntegrand ψ n π b v' w u := by
  unfold whittakerPairingIntegrand
  rw [← b.conj_inner_symm, b.add_left, map_add]
  simp only [b.conj_inner_symm, add_mul]

theorem whittakerPairingIntegrand_add_right (v w w' : V)
    (u : upperUnipotent (n + 1) F) :
    whittakerPairingIntegrand ψ n π b v (w + w') u =
      whittakerPairingIntegrand ψ n π b v w u +
        whittakerPairingIntegrand ψ n π b v w' u := by
  simp only [whittakerPairingIntegrand, map_add, b.add_left, add_mul]

variable [MeasurableSpace (upperUnipotent (n + 1) F)]
variable (ℓ : glFunctionals ψ n π) (dn : Measure (upperUnipotent (n + 1) F))

/-- The normalized pairing relation of Lemma 1.1, including ordinary scalar
integrability for every pair of vectors. Haar properties, nonzero functional,
and the hypotheses needed for existence are separate inputs. -/
def IsWhittakerPairingNormalized : Prop :=
  ∀ v w : V, Integrable (whittakerPairingIntegrand ψ n π b v w) dn ∧
    (∫ u, whittakerPairingIntegrand ψ n π b v w u ∂dn) =
      ℓ.val v * starRingEnd ℂ (ℓ.val w)

variable {ψ n π b ℓ dn}

/-- Integrability is part of the relation, not inferred from total integration. -/
theorem IsWhittakerPairingNormalized.integrable
    (h : IsWhittakerPairingNormalized ψ n π b ℓ dn) (v w : V) :
    Integrable (whittakerPairingIntegrand ψ n π b v w) dn := (h v w).1

theorem IsWhittakerPairingNormalized.integral_eq
    (h : IsWhittakerPairingNormalized ψ n π b ℓ dn) (v w : V) :
    (∫ u, whittakerPairingIntegrand ψ n π b v w u ∂dn) =
      ℓ.val v * starRingEnd ℂ (ℓ.val w) := (h v w).2

/-- A nonzero Whittaker functional excludes the zero measure from this relation. -/
theorem IsWhittakerPairingNormalized.measure_ne_zero
    (h : IsWhittakerPairingNormalized ψ n π b ℓ dn) (hℓ : ℓ.val ≠ 0) :
    dn ≠ 0 := by
  intro hdn
  apply hℓ
  ext v
  have hv := h.integral_eq v v
  rw [hdn, integral_zero_measure] at hv
  have hz : ℓ.val v = 0 := by
    rcases mul_eq_zero.mp hv.symm with hz | hz
    · exact hz
    · simpa using hz
  exact hz

end Langlands.Shahidi
