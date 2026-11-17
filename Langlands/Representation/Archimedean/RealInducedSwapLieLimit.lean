import Langlands.Representation.Archimedean.ComplexBlockRestriction
import Langlands.Representation.Archimedean.RealInducedSwapShifted
import Langlands.Representation.Archimedean.RealBlockMultiplierAnalytic
import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-!
# Lie equivariance of limits of shifted four-crossing maps

A shifted map `shiftedMap d e h`, built from four crossings whose recurrence parameters are
moved by `z`, has the recurrence parameters of an honest zero-shift map for the first block
with exponent moved by `z`. On `O(4)` the two maps agree. Hence a family of maps between the
fixed source and target modules that is weakly continuous at `0` and eventually equal to
shifted maps along a filter approaching `0` intertwines the fixed actions at `0`.
-/

noncomputable section

open scoped Topology
open Filter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
namespace RealInducedSwapLieLimit

open Langlands.LocalFactor.Archimedean
open RealBlockFrobeniusMap RealCharacterPair RealCharacterPairReducible
open RealCharacterInducedSwap RealInducedSwapGeneric RealInducedSwapShifted
open RealExponentDeformation GramFormula

/-- The complex character data with the weight of `d` and exponent moved by `z`. -/
abbrev moved (d : ComplexCharacterData) (z : ℂ) : ComplexCharacterData :=
  ComplexBlock.twist z d

@[simp]
theorem moved_weight (d : ComplexCharacterData) (z : ℂ) : (moved d z).weight = d.weight :=
  rfl

@[simp]
theorem moved_exponent (d : ComplexCharacterData) (z : ℂ) :
    (moved d z).exponent = d.exponent + z :=
  rfl

/-- A crossing with recurrence parameter moved by `z` is an unshifted crossing for a first
character of the same parity whose exponent is moved by `z`. -/
def crossingAtZero {x x' y : RealCharacterData} {z : ℂ} (h : Crossing x y z)
    (hp : x'.parity = x.parity) (he : x'.exponent = x.exponent + z) : Crossing x' y 0 where
  μ := h.μ
  symm := by
    have hpar : pairParity y x' = pairParity y x := by
      unfold pairParity
      rw [hp]
    unfold sigma0
    rw [hpar]
    exact h.symm
  recurrent := by
    have hpar : pairParity y x' = pairParity y x := by
      unfold pairParity
      rw [hp]
    have hparam : x'.exponent - y.exponent + 1 + 0 = x.exponent - y.exponent + 1 + z := by
      rw [he]
      ring
    rw [hpar, hparam]
    exact h.recurrent

variable (d e : ComplexCharacterData)

/-- Moving the four recurrence parameters by `z` is the same as moving the exponent of the
first induction block by `z` with zero shift. -/
def atZero {z : ℂ} (h : FourCrossings d e z) : FourCrossings (moved d z) e 0 where
  bc := crossingAtZero h.bc rfl (by simp only [chB_exponent, moved_exponent, moved_weight]; ring)
  ac := crossingAtZero h.ac rfl (by simp only [chA_exponent, moved_exponent, moved_weight]; ring)
  bd := crossingAtZero h.bd rfl (by simp only [chB_exponent, moved_exponent, moved_weight]; ring)
  ad := crossingAtZero h.ad rfl (by simp only [chA_exponent, moved_exponent, moved_weight]; ring)

/-- On `O(4)`, the shifted map for `d` and the unshifted map for the moved block agree on
inputs agreeing on `O(4)`. -/
theorem shiftedMap_eqOn {z : ℂ} (h : FourCrossings d e z) {f : KF 4 (source d e)}
    {f' : KF 4 (source (moved d z) e)}
    (hf : Set.EqOn (f' : Langlands.GeneralLinear 4 ℝ → ℂ) f (unitaryCompact ℝ 4)) :
    Set.EqOn (shiftedMap (moved d z) e (atZero d e h) f' :
        Langlands.GeneralLinear 4 ℝ → ℂ)
      (shiftedMap d e h f) (unitaryCompact ℝ 4) := by
  have h0 : Set.EqOn
      ((Submodule.inclusion (source_le_expanded (moved d z) e) f' :
        KF 4 (expanded (moved d z) e)) : Langlands.GeneralLinear 4 ℝ → ℂ)
      (Submodule.inclusion (source_le_expanded d e) f : KF 4 (expanded d e))
      (unitaryCompact ℝ 4) := hf
  have h1 := blockFrobMap_eqOn (dataBC d e h) (dataBC (moved d z) e (atZero d e h)) h0
  have h2 := blockFrobMap_eqOn (dataAC d e h) (dataAC (moved d z) e (atZero d e h)) h1
  have h3 := blockFrobMap_eqOn (dataBD d e h) (dataBD (moved d z) e (atZero d e h)) h2
  exact blockFrobMap_eqOn (dataAD d e h) (dataAD (moved d z) e (atZero d e h)) h3

/-- The source of the moved block is the source moved by `z` in its first two positions. -/
theorem isExponentShift_source (z : ℂ) :
    IsExponentShift 4 (source d e) (source (moved d z) e) ![1, 1, 0, 0] z :=
  IsExponentShift.of_forall₂ rfl
    (List.Forall₂.cons (show d.weight = (moved d z).weight from rfl)
      (List.Forall₂.cons (show e.weight = e.weight from rfl) List.Forall₂.nil))
    (by
      intro i
      fin_cases i <;>
        simp [realPositionExponent, moved_exponent, moved_weight] <;> ring)

/-- The target of the moved block is the target moved by `z` in its last two positions. -/
theorem isExponentShift_target (z : ℂ) :
    IsExponentShift 4 (target d e) (target (moved d z) e) ![0, 0, 1, 1] z :=
  IsExponentShift.of_forall₂ rfl
    (List.Forall₂.cons (show e.weight = e.weight from rfl)
      (List.Forall₂.cons (show d.weight = (moved d z).weight from rfl) List.Forall₂.nil))
    (by
      intro i
      fin_cases i <;>
        simp [realPositionExponent, moved_exponent, moved_weight] <;> ring)

/-- The zero-shift map for the moved block is an intertwiner. -/
theorem isRealStandardIntertwiner_atZero {z : ℂ} (h : FourCrossings d e z) :
    IsRealStandardIntertwiner 4 (realStandardRep 4 (target (moved d z) e))
      (realStandardLie 4 (target (moved d z) e)) (source (moved d z) e)
      (shiftedMap (moved d z) e (atZero d e h)) :=
  isRealStandardIntertwiner_of_modulo_bot
    (shiftedMap_zero_modulo (moved d z) e (atZero d e h))

/-- **Limits of shifted maps.** A family of maps between the fixed source and target modules,
weakly continuous at `0` along a nontrivial filter `L ≤ 𝓝 0` and eventually in `L` equal to a
shifted map at a nonzero shift, is an intertwiner at `0`. -/
theorem isRealStandardIntertwiner_of_tendsto_shifted {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (S : ℂ → KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e))
    (hS : ∀ (f : KF 4 (source d e)) (ℓ : KF 4 (target d e) →ₗ[ℂ] ℂ),
      Tendsto (fun z => ℓ (S z f)) L (𝓝 (ℓ (S 0 f))))
    (hev : ∀ᶠ z in L, z ≠ 0 ∧ ∃ h : FourCrossings d e z, S z = shiftedMap d e h) :
    IsRealStandardIntertwiner 4 (realStandardRep 4 (target d e)) (realStandardLie 4 (target d e))
      (source d e) (S 0) := by
  refine isRealStandardIntertwiner_of_tendsto (ds' := fun z => source (moved d z) e)
    (es' := fun z => target (moved d z) e) (a := ![1, 1, 0, 0]) (b := ![0, 0, 1, 1])
    hL S hS ?_
  filter_upwards [hev] with z hz
  obtain ⟨hz0, h, hSz⟩ := hz
  refine ⟨hz0, isExponentShift_source d e z, isExponentShift_target d e z,
    shiftedMap (moved d z) e (atZero d e h),
    isRealStandardIntertwiner_atZero d e h, fun f f' hf => ?_⟩
  rw [hSz]
  exact shiftedMap_eqOn d e h hf

/-- The same conclusion for a weakly analytic family. -/
theorem isRealStandardIntertwiner_of_weaklyAnalytic {L : Filter ℂ} [L.NeBot] (hL : L ≤ 𝓝 0)
    (S : ℂ → KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e))
    (hS : ∀ f : KF 4 (source d e),
      RealBlockMultiplierAnalytic.IsWeaklyAnalyticAt (fun z => S z f) 0)
    (hev : ∀ᶠ z in L, z ≠ 0 ∧ ∃ h : FourCrossings d e z, S z = shiftedMap d e h) :
    IsRealStandardIntertwiner 4 (realStandardRep 4 (target d e)) (realStandardLie 4 (target d e))
      (source d e) (S 0) :=
  isRealStandardIntertwiner_of_tendsto_shifted d e hL S
    (fun f ℓ => (hS f ℓ).continuousAt.tendsto.mono_left hL) hev

/-- An injective value at `0` of such a weakly analytic family gives the swap. -/
theorem realInjectiveIntertwinerExists_of_weaklyAnalytic {L : Filter ℂ} [L.NeBot]
    (hL : L ≤ 𝓝 0) (S : ℂ → KF 4 (source d e) →ₗ[ℂ] KF 4 (target d e))
    (hS : ∀ f : KF 4 (source d e),
      RealBlockMultiplierAnalytic.IsWeaklyAnalyticAt (fun z => S z f) 0)
    (hev : ∀ᶠ z in L, z ≠ 0 ∧ ∃ h : FourCrossings d e z, S z = shiftedMap d e h)
    (hinj : Function.Injective (S 0)) :
    RealInjectiveIntertwinerExists 4 (source d e) (target d e) :=
  ⟨S 0, hinj, isRealStandardIntertwiner_of_weaklyAnalytic d e hL S hS hev⟩

end RealInducedSwapLieLimit
end Langlands.Archimedean
