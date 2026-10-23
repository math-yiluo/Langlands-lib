import Langlands.Group.GL.UpperBruhatEmbedding
import Langlands.Representation.Unitary.Basic
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Analysis.Local.QuotientMeasure

/-!
# The lower-right Kirillov pairing quotient

This uses the upper-unipotent subgroup in the lower-right block. The paired
Markdown records the literal primed-subgroup discrepancy in Proposition 1.2
of Shahidi (1984); no invariance under its literal lower subgroup is assumed.
-/

noncomputable section

namespace Langlands.Shahidi

open MeasureTheory GeneralLinear Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The actual lower-right inclusion `g ↦ diag(1,g)`, including rank zero. -/
abbrev kirillovInclusion (n : ℕ) :
    Langlands.GeneralLinear n F →* Langlands.GeneralLinear (n + 1) F :=
  Bruhat.insert 0

omit [TopologicalSpace F] in
@[simp] theorem kirillovInclusion_succ_succ {n : ℕ}
    (g : Langlands.GeneralLinear n F) (i j : Fin n) :
    kirillovInclusion n g i.succ j.succ = g i j := by
  simpa only [Fin.succAbove_zero] using
    Bruhat.insert_succAbove_succAbove (0 : Fin (n + 1)) g i j

/-- The smaller group's upper unipotents remain upper unipotent in the
lower-right block of the larger group. -/
def kirillovUnipotent {n : ℕ} (u : upperUnipotent n F) :
    upperUnipotent (n + 1) F :=
  ⟨kirillovInclusion n u.val, by
    constructor
    · exact Bruhat.insert_upper 0 u.val u.property.1
    · intro i
      induction i using Fin.succAboveCases (0 : Fin (n + 1)) with
      | x => exact Bruhat.insert_p_p 0 u.val
      | p i =>
        change Bruhat.insert 0 u.val ((0 : Fin (n + 1)).succAbove i)
          ((0 : Fin (n + 1)).succAbove i) = 1
        rw [Bruhat.insert_succAbove_succAbove]
        exact UpperUnipotent.entry_diag u i⟩

omit [TopologicalSpace F] in
/-- The chosen smaller group is embedded faithfully. -/
theorem kirillovInclusion_injective (n : ℕ) :
    Function.Injective (kirillovInclusion (F := F) n) := by
  intro g h he
  apply Units.ext
  ext i j
  have hij := congrArg (fun k : Langlands.GeneralLinear (n + 1) F =>
    k i.succ j.succ) he
  simpa only [kirillovInclusion_succ_succ] using hij

/-- The actual left quotient of the smaller group by its upper unipotents.
Through `kirillovInclusion` these are the upper unipotents in the lower-right
block, not the longest-Weyl conjugates of the upper-left upper unipotents. -/
abbrev KirillovQuotient (n : ℕ) (F : Type uF) [Field F] :=
  QuotientIntegration.LeftQuotient (upperUnipotent n F)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F) (n : ℕ)
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
variable (ℓ : glFunctionals ψ n π)

/-- The product of the two actual Whittaker coefficients restricted to the
lower-right block, conjugating the second coefficient. -/
def kirillovPairingFunction (v w : V) (g : Langlands.GeneralLinear n F) : ℂ :=
  ℓ.val (π (kirillovInclusion n g) v) *
    starRingEnd ℂ (ℓ.val (π (kirillovInclusion n g) w))

/-- Unitarity of the common character cancels the two equivariance factors. -/
theorem kirillovPairingFunction_invariant (v w : V) (u : upperUnipotent n F)
    (g : Langlands.GeneralLinear n F) :
    kirillovPairingFunction ψ n π ℓ v w (u.val * g) =
      kirillovPairingFunction ψ n π ℓ v w g := by
  unfold kirillovPairingFunction
  rw [map_mul, map_mul]
  change ℓ.val (π (kirillovUnipotent u).val (π (kirillovInclusion n g) v)) *
    starRingEnd ℂ (ℓ.val (π (kirillovUnipotent u).val
      (π (kirillovInclusion n g) w))) = _
  rw [ℓ.property, ℓ.property, map_mul, mul_mul_mul_comm]
  have hc : (standardCharacter ψ n (kirillovUnipotent u) : ℂ) *
      starRingEnd ℂ (standardCharacter ψ n (kirillovUnipotent u) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_standardCharacter]
    norm_num
  rw [hc, one_mul]

/-- Representative-independent scalar integrand on the actual left quotient. -/
def kirillovPairingIntegrand (v w : V) : KirillovQuotient n F → ℂ :=
  QuotientIntegration.descend _ (kirillovPairingFunction ψ n π ℓ v w)
    (kirillovPairingFunction_invariant ψ n π ℓ v w)

@[simp] theorem kirillovPairingIntegrand_mk (v w : V)
    (g : Langlands.GeneralLinear n F) :
    kirillovPairingIntegrand ψ n π ℓ v w (Quotient.mk _ g) =
      ℓ.val (π (kirillovInclusion n g) v) *
        starRingEnd ℂ (ℓ.val (π (kirillovInclusion n g) w)) := rfl

variable [MeasurableSpace (KirillovQuotient n F)]
variable (b : InvariantPositiveForm π) (ν : Measure (KirillovQuotient n F))

/-- The Proposition 1.2 pairing equation for the documented lower-right upper
quotient interpretation, with scalar integrability explicit. This does not
assert existence, invariance or Weil compatibility of the supplied measure. -/
def IsKirillovPairingNormalized : Prop :=
  ∀ v w : V, Integrable (kirillovPairingIntegrand ψ n π ℓ v w) ν ∧
    (∫ q, kirillovPairingIntegrand ψ n π ℓ v w q ∂ν) = b.inner w v

variable {ψ n π ℓ b ν}

theorem IsKirillovPairingNormalized.integrable
    (h : IsKirillovPairingNormalized ψ n π ℓ b ν) (v w : V) :
    Integrable (kirillovPairingIntegrand ψ n π ℓ v w) ν := (h v w).1

theorem IsKirillovPairingNormalized.integral_eq
    (h : IsKirillovPairingNormalized ψ n π ℓ b ν) (v w : V) :
    (∫ q, kirillovPairingIntegrand ψ n π ℓ v w q ∂ν) = b.inner w v := (h v w).2

/-- A nonzero vector and positive definiteness exclude the zero quotient measure. -/
theorem IsKirillovPairingNormalized.measure_ne_zero
    (h : IsKirillovPairingNormalized ψ n π ℓ b ν) (v : V) (hv : v ≠ 0) :
    ν ≠ 0 := by
  intro hν
  have hh := h.integral_eq v v
  rw [hν, integral_zero_measure] at hh
  exact hv (b.definite v hh.symm)

end Langlands.Shahidi
