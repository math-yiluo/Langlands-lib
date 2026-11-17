import Langlands.Representation.Archimedean.RealInducedSwapGerm

/-!
# Generic paths and specialization of the regular crossing maps

Pure imaginary shifts provide a nontrivial generic path when the central
exponents have equal imaginary parts. Generic identities specialize the ambient
and compact-action values of the target-valued regular family.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapLimit

open Langlands.LocalFactor.Archimedean
open RealBlockMultiplier RealBlockMultiplierAnalytic RealFiniteLayerRegularization
open RealCharacterInducedSwap RealInducedSwapGeneric RealInducedSwapInverse
open RealInducedSwapRegularizedFamily RealInducedSwapRegularization RealInducedSwapGerm
open scoped Topology

/-- A nontrivial filter approaching zero through nonzero generic shifts. -/
def HasGenericPath (d e : ComplexCharacterData) : Prop :=
  ∃ L : Filter ℂ, L.NeBot ∧ L ≤ 𝓝 0 ∧
    ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z

theorem genericParameter_of_im_ne_zero {ν : ℂ} {ε : ℤ} (hν : ν.im ≠ 0) :
    IsGenericParameter ν ε := by
  constructor <;> intro m h <;> apply hν <;>
    simpa using congrArg Complex.im h

theorem genericShift_of_im_ne_zero (d e : ComplexCharacterData) {z : ℂ}
    (him : (d.exponent - e.exponent + z).im ≠ 0) :
    IsGenericShift d e z := by
  refine ⟨genericParameter_of_im_ne_zero ?_, genericParameter_of_im_ne_zero ?_,
    genericParameter_of_im_ne_zero ?_, genericParameter_of_im_ne_zero ?_⟩ <;>
    simpa [chA_exponent, chB_exponent] using him

/-- The image of the positive real neighborhood filter under `r ↦ r I`. -/
theorem hasGenericPath_of_im_eq (d e : ComplexCharacterData)
    (him : d.exponent.im = e.exponent.im) : HasGenericPath d e := by
  let L : Filter ℂ := Filter.map (fun r : ℝ => (r : ℂ) * Complex.I) (𝓝[>] 0)
  have hne : L.NeBot := by dsimp [L]; infer_instance
  have hc : ContinuousAt (fun r : ℝ => (r : ℂ) * Complex.I) 0 := by fun_prop
  have hL : L ≤ 𝓝 0 := by
    have ht : Filter.Tendsto (fun r : ℝ => (r : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Complex.ofReal_zero, zero_mul] using
        hc.tendsto.mono_left nhdsWithin_le_nhds
    exact ht
  refine ⟨L, hne, hL, ?_⟩
  change ∀ᶠ r : ℝ in 𝓝[>] 0,
    (r : ℂ) * Complex.I ≠ 0 ∧ IsGenericShift d e ((r : ℂ) * Complex.I)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : r ≠ 0 := ne_of_gt hr
  refine ⟨?_, genericShift_of_im_ne_zero d e ?_⟩
  · intro hz
    exact hr' (by simpa using congrArg Complex.im hz)
  · simpa [him] using hr'

variable (d e : ComplexCharacterData) (c : Choices)
    (hc : Valid d e c) (hreg : Admissible d e c)
    {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (hpath : ∀ᶠ z in L, z ≠ 0 ∧ IsGenericShift d e z)

include hreg hL hpath

/-- At zero the target-valued projection has the actual ambient regular value. -/
theorem inclusion_regularTargetMap_zero (f : KF 4 (source d e)) :
    Submodule.inclusion (source_le_expanded e d) (regularTargetMap d e c hc 0 f) =
      regularMap d e c hc 0 f := by
  apply eq_of_weaklyAnalyticAt_eventuallyEq
    ((regularTargetMap_analytic d e c hc hreg f).map
      (Submodule.inclusion (source_le_expanded e d)))
    (regularMap_analytic d e c hc hreg f) hL
  filter_upwards [hpath] with z hz
  rw [regularTargetMap_eq_generic d e c hc hreg hz.1 hz.2,
    regularMap_eq_generic d e c hc hreg hz.1 hz.2]
  rfl

/-- The ambient regular value belongs to the actual target induction module. -/
theorem regularMap_mem_target_zero (f : KF 4 (source d e)) :
    (regularMap d e c hc 0 f : Langlands.GeneralLinear 4 ℝ → ℂ) ∈
      KF 4 (target d e) := by
  rw [← inclusion_regularTargetMap_zero d e c hc hreg hL hpath f]
  exact (regularTargetMap d e c hc 0 f).2

/-- Compact equivariance at the center follows from its generic identity. -/
theorem regularTargetMap_zero_rightTranslation
    (k : Matrix.unitaryGroup (Fin 4) ℝ) (f : KF 4 (source d e)) :
    regularTargetMap d e c hc 0 (realStandardRep 4 (source d e) k f) =
      realStandardRep 4 (target d e) k (regularTargetMap d e c hc 0 f) := by
  apply eq_of_weaklyAnalyticAt_eventuallyEq
    (regularTargetMap_analytic d e c hc hreg (realStandardRep 4 (source d e) k f))
    ((regularTargetMap_analytic d e c hc hreg f).map
      (realStandardRep 4 (target d e) k)) hL
  filter_upwards [hpath] with z hz
  rw [regularTargetMap_eq_generic d e c hc hreg hz.1 hz.2]
  exact RealInducedSwapShifted.shiftedMap_rightTranslation d e
    (genericFourCrossings hz.2) k f

end RealInducedSwapLimit
end Langlands.Archimedean
