import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Haar character of an involutive continuous automorphism -/

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG

/-- An involutive continuous automorphism has Haar modulus one. -/
theorem mulEquivHaarChar_eq_one_of_involutive
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ* G) (he : Function.Involutive e) :
    mulEquivHaarChar e = 1 := by
  have hee : e.trans e = ContinuousMulEquiv.refl G := by
    ext g
    exact he g
  have hsq : mulEquivHaarChar e * mulEquivHaarChar e = 1 := by
    rw [← mulEquivHaarChar_trans, hee, mulEquivHaarChar_refl]
  apply NNReal.coe_injective
  apply (pow_eq_one_iff_of_nonneg (NNReal.coe_nonneg _) (by decide : 2 ≠ 0)).mp
  simpa only [pow_two, NNReal.coe_mul, NNReal.coe_one] using
    congrArg (fun c : ℝ≥0 => (c : ℝ)) hsq

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
