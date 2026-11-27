import Langlands.HarmonicAnalysis.UnitConjugation.LatticeTests
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier

/-! # Fourier transforms of lattice coset tests -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Set

section Bicharacter

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
  {e : X → X → ℂ} (he : IsSelfDualBicharacter e)
  (L : AddSubgroup X) (hLo : IsOpen (L : Set X)) (hLc : IsCompact (L : Set X))

/-- Fourier transformation of the indicator of `z + L` gives the character at `z`
multiplied by the Haar volume of `L` and restricted to its annihilator. -/
def FourierLatticeCosetStatement : Prop :=
  ∀ z x, bicharacterFourierSB μ he (latticeCosetTest L hLo hLc z) x =
    (he.annihilator (L : Set X) : Set X).indicator (fun x => e x z * (μ.real L : ℂ)) x

theorem fourierLatticeCoset : FourierLatticeCosetStatement μ he L hLo hLc := by
  intro z x
  have htranslate (y : X) : latticeCosetTest L hLo hLc z (z + y) =
      (L : Set X).indicator (fun _ => (1 : ℂ)) y := by
    rw [latticeCosetTest_apply, map_add]
    have hquot : QuotientAddGroup.mk' L z + QuotientAddGroup.mk' L y =
        QuotientAddGroup.mk' L z ↔ y ∈ L := by
      rw [← QuotientAddGroup.eq_zero_iff]
      constructor
      · intro h
        exact add_left_cancel (h.trans (add_zero _).symm)
      · intro h
        change QuotientAddGroup.mk' L y = 0 at h
        rw [h, add_zero]
    by_cases hy : y ∈ L
    · rw [ite_eq_left (hquot.mpr hy), indicator_of_mem hy]
    · rw [ite_eq_right (hquot.not.mpr hy), indicator_of_notMem hy]
  change bicharacterFourier μ e (latticeCosetTest L hLo hLc z) x = _
  calc
    _ = e x z * bicharacterFourier μ e ((L : Set X).indicator fun _ => (1 : ℂ)) x := by
      rw [bicharacterFourier_apply, bicharacterFourier_apply,
        ← integral_add_left_eq_self (fun y => e x y * latticeCosetTest L hLo hLc z y) z,
        ← integral_const_mul]
      congr 1
      funext y
      rw [he.map_add_right, htranslate, mul_assoc]
    _ = _ := by
      rw [BicharacterFourier.Internal.bicharacterFourier_indicator μ he L hLo]
      by_cases hx : x ∈ he.annihilator (L : Set X)
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

end Bicharacter

namespace UnitConjugation

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V]
  [IsModuleTopology F V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
  (ψ : UnitaryAdditiveCharacter F) {B : LinearMap.BilinForm F V}
  (hs : B.IsSymm) (hn : B.Nondegenerate) (μ : AdditiveHaarMeasure V)
  (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V))

/-- The Fourier transform of a lattice coset indicator for the pairing convention
`(X, Z) ↦ ψ(B(X, Z))`. -/
theorem pairingFourierSB_latticeCosetTest_apply (z x : V) :
    pairingFourierSB ψ hs hn μ (latticeCosetTest L hLo hLc z) x =
      ((isSelfDualBicharacter_pairingCharacter ψ hs hn).annihilator (L : Set V) : Set V).indicator
        (fun x => (ψ (B x z) : ℂ) * (μ.measure.real L : ℂ)) x := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  simpa only [pairingFourierSB_apply, bicharacterFourier_apply, coe_bicharacterFourierSB,
    pairingCharacter_apply] using
    fourierLatticeCoset μ.measure (isSelfDualBicharacter_pairingCharacter ψ hs hn) L hLo hLc z x

end UnitConjugation

end Langlands.HarmonicAnalysis
