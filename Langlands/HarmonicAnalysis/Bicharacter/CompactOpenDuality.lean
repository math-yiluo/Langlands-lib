import Langlands.HarmonicAnalysis.Bicharacter.Fourier

/-! # Annihilators of compact open subgroups for self-dual bicharacters -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Set
open scoped Topology

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  {e : X → X → ℂ} (he : IsSelfDualBicharacter e)
  (L : AddSubgroup X)

/-- The annihilator of a compact open additive subgroup is compact. -/
theorem IsSelfDualBicharacter.isCompact_annihilator_compactOpen
    (hLo : IsOpen (L : Set X)) (hLc : IsCompact (L : Set X)) :
    IsCompact (he.annihilator (L : Set X) : Set X) := by
  obtain ⟨K, hK, hKA⟩ := he.big (L : Set X) (hLo.mem_nhds L.zero_mem)
  exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (he.isOpen_annihilator hLc))
    fun y hy => hKA y hy

variable [compactX : LocallyCompactSpace X] [countableX : SecondCountableTopology X]
  [exhaustionX : CompactOpenExhaustion X] [MeasurableSpace X] [borelX : BorelSpace X]
  (μ : Measure X) [haarμ : μ.IsAddHaarMeasure]

/-- For a self-dual bicharacter, the annihilator of the annihilator of a compact
open subgroup is the original subgroup. -/
def CompactOpenDoubleAnnihilatorStatement [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [CompactOpenExhaustion X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  IsOpen (L : Set X) → IsCompact (L : Set X) →
    he.annihilator (he.annihilator (L : Set X) : Set X) = L

include haarμ in
/-- Fourier inversion recovers the indicator of the original subgroup after the
indicator calculation has identified the support of its second transform. -/
theorem compactOpenDoubleAnnihilator : CompactOpenDoubleAnnihilatorStatement he L := by
  intro hLo hLc
  let A := he.annihilator (L : Set X)
  let B := he.annihilator (A : Set X)
  have hAo : IsOpen (A : Set X) := he.isOpen_annihilator hLc
  have hAc : IsCompact (A : Set X) := he.isCompact_annihilator_compactOpen L hLo hLc
  let φ := (L : Set X).indicator (fun _ => (1 : ℂ))
  obtain ⟨C, _, hInv⟩ := exists_pos_bicharacterFourier_bicharacterFourier μ he
  have hFormula (x : X) :
      (bicharacterFourier μ e (bicharacterFourier μ e φ)) x =
        (B : Set X).indicator (fun _ => (μ.real L : ℂ) * (μ.real A : ℂ)) x := by
    have h₀ : bicharacterFourier μ e φ = (fun z => (μ.real L : ℂ) *
        (A : Set X).indicator (fun _ => (1 : ℂ)) z) := by
      funext z
      rw [BicharacterFourier.Internal.bicharacterFourier_indicator μ he L hLo]
      by_cases hz : z ∈ A
      · rw [indicator_of_mem hz, indicator_of_mem hz, mul_one]
      · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]
    rw [h₀, bicharacterFourier_apply]
    simp_rw [mul_left_comm (e x _), integral_const_mul, ← bicharacterFourier_apply]
    rw [BicharacterFourier.Internal.bicharacterFourier_indicator μ he A hAo]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  change B = L
  ext x
  constructor
  · intro hx
    by_contra hxNot
    have hneg : -x ∉ L := fun h => hxNot (by simpa only [neg_neg] using L.neg_mem h)
    have h₁ := hFormula x
    have h₂ := hInv φ (indicator_one_mem_schwartzBruhatSubmodule L hLc hLo) x
    rw [indicator_of_mem hx] at h₁
    rw [h₁, show φ (-x) = 0 from indicator_of_notMem hneg _, mul_zero] at h₂
    have hLpos : 0 < μ.real (L : Set X) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLc.measure_lt_top.ne
    have hApos : 0 < μ.real (A : Set X) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (hAo.measure_pos μ ⟨0, A.zero_mem⟩).ne' hAc.measure_lt_top.ne
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hLpos.ne') (Complex.ofReal_ne_zero.mpr hApos.ne')) h₂
  · intro hx y hy
    exact (he.symm _ _).trans (he.mem_annihilator.mp hy x hx)

end Langlands.HarmonicAnalysis
