import Langlands.Representation.Archimedean.RealInducedSwapLieLimit

/-!
# Limits of scalar multiples of shifted four-crossing maps

Normalized regular families equal scalar multiples `c(z) • shiftedMap d e h` of the shifted
maps at generic nonzero shifts. A scalar multiple of an intertwiner is an intertwiner, so the
limit theorem of `RealInducedSwapLieLimit` extends to such families.
-/

noncomputable section

open scoped Topology TensorProduct
open Filter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealInducedSwapScalarLimit

open Langlands.LocalFactor.Archimedean
open RealInducedSwapGeneric RealInducedSwapShifted RealExponentDeformation RealInducedSwapLieLimit

/-- A scalar multiple of an intertwiner is an intertwiner. -/
theorem isRealStandardIntertwiner_smul {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {ds : List RealBlock}
    {B : KF n ds →ₗ[ℂ] V} (hB : IsRealStandardIntertwiner n ρ π ds B) (c : ℂ) :
    IsRealStandardIntertwiner n ρ π ds (c • B) := by
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, h⟩ := hB.1 k f
    exact ⟨hf, by rw [LinearMap.smul_apply, LinearMap.smul_apply, h, map_smul]⟩
  · obtain ⟨hf, h⟩ := hB.2 X f
    exact ⟨hf, by rw [LinearMap.smul_apply, LinearMap.smul_apply, h, map_smul]⟩

variable (d e : ComplexCharacterData)

/-- **Limits of scalar multiples of shifted maps.** A family of maps between the fixed source
and target modules, weakly continuous at `0` along a nontrivial filter `L ≤ 𝓝 0` and eventually
in `L` equal to a scalar multiple of a shifted map at a nonzero shift, is an intertwiner at
`0`. -/
theorem isRealStandardIntertwiner_of_tendsto_smul {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (S : ℂ → KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e))
    (hS : ∀ (f : KF 4 (source d e)) (ℓ : KF 4 (target d e) →ₗ[ℂ] ℂ),
      Tendsto (fun z => ℓ (S z f)) L (𝓝 (ℓ (S 0 f))))
    (hev : ∀ᶠ z in L, z ≠ 0 ∧
      ∃ (c : ℂ) (h : FourCrossings d e z), S z = c • shiftedMap d e h) :
    IsRealStandardIntertwiner 4 (realStandardRep 4 (target d e)) (realStandardLie 4 (target d e))
      (source d e) (S 0) := by
  refine isRealStandardIntertwiner_of_tendsto (ds' := fun z => source (moved d z) e)
    (es' := fun z => target (moved d z) e) (a := ![1, 1, 0, 0]) (b := ![0, 0, 1, 1])
    hL S hS ?_
  filter_upwards [hev] with z hz
  obtain ⟨hz0, c, h, hSz⟩ := hz
  refine ⟨hz0, isExponentShift_source d e z, isExponentShift_target d e z,
    c • shiftedMap (moved d z) e (atZero d e h),
    isRealStandardIntertwiner_smul (isRealStandardIntertwiner_atZero d e h) c,
    fun f f' hf g hg => ?_⟩
  rw [hSz]
  change c * (shiftedMap (moved d z) e (atZero d e h) f' : Langlands.GeneralLinear 4 ℝ → ℂ) g =
    c * (shiftedMap d e h f : Langlands.GeneralLinear 4 ℝ → ℂ) g
  rw [shiftedMap_eqOn d e h hf hg]

/-- The same conclusion for a weakly analytic family. -/
theorem isRealStandardIntertwiner_of_weaklyAnalytic_smul {L : Filter ℂ} [L.NeBot]
    (hL : L ≤ 𝓝 0) (S : ℂ → KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e))
    (hS : ∀ f : KF 4 (source d e),
      RealBlockMultiplierAnalytic.IsWeaklyAnalyticAt (fun z => S z f) 0)
    (hev : ∀ᶠ z in L, z ≠ 0 ∧
      ∃ (c : ℂ) (h : FourCrossings d e z), S z = c • shiftedMap d e h) :
    IsRealStandardIntertwiner 4 (realStandardRep 4 (target d e)) (realStandardLie 4 (target d e))
      (source d e) (S 0) :=
  isRealStandardIntertwiner_of_tendsto_smul d e hL S
    (fun f ℓ => (hS f ℓ).continuousAt.tendsto.mono_left hL) hev

/-- An injective value at `0` of such a weakly analytic family gives the swap. -/
theorem realInjectiveIntertwinerExists_of_weaklyAnalytic_smul {L : Filter ℂ} [L.NeBot]
    (hL : L ≤ 𝓝 0) (S : ℂ → KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e))
    (hS : ∀ f : KF 4 (source d e),
      RealBlockMultiplierAnalytic.IsWeaklyAnalyticAt (fun z => S z f) 0)
    (hev : ∀ᶠ z in L, z ≠ 0 ∧
      ∃ (c : ℂ) (h : FourCrossings d e z), S z = c • shiftedMap d e h)
    (hinj : Function.Injective (S 0)) :
    RealInjectiveIntertwinerExists 4 (source d e) (target d e) :=
  ⟨S 0, hinj, isRealStandardIntertwiner_of_weaklyAnalytic_smul d e hL S hS hev⟩

end RealInducedSwapScalarLimit
end Langlands.Archimedean
