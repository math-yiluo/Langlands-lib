import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.AllField.Group.GL.UnramifiedCharacter
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
/-!
# Determinant slices and equal-rank slice coefficients

JPSS (1983), Section 4.2, (4.2.1): the determinant fibers `|det g| = q^(-m)` of
the actual quotient `N_(n+1) \ GL_(n+1)` and the restricted integrals over them.
The measure is supplied. No convergence, support bound, compactness, or series
expansion of the full integral is asserted.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_ord_units normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis
open MeasureTheory

universe uF

section General

variable {F : Type uF} [Field F]

end General

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The normalized order is continuous from the field units into the discrete integers. -/
theorem continuous_ord_units :
    letI := T.topology
    Continuous (fun a : Fˣ => T.ord (a : F)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [continuous_discrete_rng]
  intro m
  rw [isOpen_iff_forall_mem_open]
  intro a ha
  refine ⟨(fun x : Fˣ => x * a⁻¹) ⁻¹' (T.normalizedAbsUnits.ker : Set Fˣ),
    ?_, T.isOpen_ker_normalizedAbsUnits.preimage (continuous_id.mul continuous_const), ?_⟩
  · intro x hx
    have hk : x * a⁻¹ ∈ T.ordUnits.ker := by
      rw [T.ker_ordUnits]
      exact hx
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    have he := congrArg Multiplicative.toAdd hk
    rw [T.ordUnits_apply, T.ordUnits_apply] at he
    exact he.trans ha
  · change a * a⁻¹ ∈ T.normalizedAbsUnits.ker
    rw [mul_inv_cancel]
    exact T.normalizedAbsUnits.ker.one_mem

section Coefficients

/-! The quotient carries the Borel measurable structure of the quotient topology induced
by `T.topology`; the supplied measure `μ` is a measure for that structure. -/

variable {n : ℕ}
variable (μ : letI := T.topology
  letI := borel (LeftUnipotentQuotient n F)
  Measure (LeftUnipotentQuotient n F))

variable {T μ}

variable (T μ)

end Coefficients

section EqualRank

variable {n : ℕ}
variable (μ : letI := T.topology
  letI := borel (LeftUnipotentQuotient n F)
  Measure (LeftUnipotentQuotient n F))

end EqualRank

end Padic

end Langlands.AllField.RankinSelberg
