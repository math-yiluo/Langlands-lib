import Langlands.BaseChange.TwistedCharacter.ConjugationAverage
import Mathlib.MeasureTheory.Integral.Prod

/-! # Local character values from constant operator averages -/

noncomputable section

namespace Langlands.BaseChange

open Filter HarmonicAnalysis HarishChandraSchwartz JacquetLanglands MeasureTheory
open scoped Topology

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (K : Subgroup G)
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

section Smearing

variable [MeasurableSpace G] [BorelSpace G]

/-- Integrating a test function where the averaged operators are constant gives the common
operator multiplied by the integral of the test function. -/
theorem conjugationAverage_integratedAction_of_eq (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (hρ : IsSmooth ρ) (A : Module.End ℂ V)
    (f : SchwartzBruhat G) {U : Set G} (hf : Function.support f ⊆ U)
    (T : Module.End ℂ V)
    (hconst : ∀ y ∈ U, conjugationAverage ρ hρ K (ρ y ∘ₗ A) = T) :
    conjugationAverage ρ hρ K (Hecke.integratedAction μ ρ hρ f ∘ₗ A) =
      (∫ y, f y ∂μ) • T := by
  apply LinearMap.ext
  intro v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  rw [map_sub, sub_eq_zero]
  let coeff (p : K × G) : ℂ :=
    ℓ (ρ (p.1 : G) (ρ p.2 (A (ρ (p.1 : G)⁻¹ v))))
  have hc : IsLocallyConstant coeff := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro p
    have hin := (Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).inv :
        Continuous fun q : K × G => (q.1 : G)⁻¹)
    have hout := ((Hecke.orbitMap_locallyConstant ρ
      (hρ (A (ρ (p.1 : G)⁻¹ v)))).comp ℓ).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).mul continuous_snd :
        Continuous fun q : K × G => (q.1 : G) * q.2)
    filter_upwards [hin.eventually_eq p, hout.eventually_eq p] with q hq hq'
    change ρ (q.1 : G)⁻¹ v = ρ (p.1 : G)⁻¹ v at hq
    change ℓ (ρ ((q.1 : G) * q.2) (A (ρ (p.1 : G)⁻¹ v))) =
      ℓ (ρ ((p.1 : G) * p.2) (A (ρ (p.1 : G)⁻¹ v))) at hq'
    simpa only [coeff, hq, map_mul, Module.End.mul_apply] using hq'
  have hs : HasCompactSupport (fun p : K × G => f p.2 * coeff p) := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_univ.prod (Hecke.TestFunction.isCompact_support f))
    intro p hp
    exact ⟨Set.mem_univ _, (mul_ne_zero_iff.mp hp).1⟩
  calc
    _ = ∫ k : K, (∫ y, f y * coeff (k, y) ∂μ) ∂(normalizedHaar K) := by
      rw [conjugationAverage_dual]
      congr 1 with k
      exact Hecke.integratedAction_dual μ ρ hρ f _ (ℓ.comp (ρ (k : G)))
    _ = ∫ y, (∫ k : K, f y * coeff (k, y) ∂(normalizedHaar K)) ∂μ :=
      integral_integral_swap_of_hasCompactSupport
        ((f.continuous.comp continuous_snd).mul hc.continuous) hs
    _ = ∫ y, f y * ℓ (conjugationAverage ρ hρ K (ρ y ∘ₗ A) v) ∂μ := by
      congr 1 with y
      rw [integral_const_mul, conjugationAverage_dual]
      rfl
    _ = (∫ y, f y ∂μ) * ℓ (T v) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : f y = 0
      · simp [hy]
      · rw [hconst y (hf hy)]
    _ = _ := by simp [smul_eq_mul]

end Smearing

section LocalValue

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- An operator average that is constant near a point has finite rank there. Its trace is the
local twisted character value for every Haar measure. -/
theorem exists_hasTwistedCharacterValue_of_eventuallyEq (hρ : IsAdmissible ρ)
    (A : Module.End ℂ V) (δ : G)
    (hconst : ∀ᶠ y in 𝓝 δ, conjugationAverage ρ hρ.1 K (ρ y ∘ₗ A) =
      conjugationAverage ρ hρ.1 K (ρ δ ∘ₗ A)) :
    ∃ c : ℂ, HasTwistedCharacterValue ρ hρ A δ c := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  let T := conjugationAverage ρ hρ.1 K (ρ δ ∘ₗ A)
  obtain ⟨U, hsub, hU, hδ⟩ := mem_nhds_iff.mp hconst
  have heq : ∀ y ∈ U, conjugationAverage ρ hρ.1 K (ρ y ∘ₗ A) = T := hsub
  obtain ⟨S, hSc, hSo, hδS, hSU⟩ := exists_isCompact_isClopen_subset hU hδ
  let f₀ := Hecke.TestFunction.characteristic hSo hSc
  let μ₀ : Measure G := Measure.haar
  have hsupp : Function.support (f₀ : G → ℂ) ⊆ U :=
    (Hecke.TestFunction.support_characteristic hSo hSc).trans_le hSU
  have hint : ∫ y, f₀ y ∂μ₀ = ((μ₀ S).toReal : ℂ) := by
    change ∫ y, S.indicator (fun _ => (1 : ℂ)) y ∂μ₀ = _
    rw [integral_indicator_const _ hSo.isClosed.measurableSet, Measure.real]
    simp
  have hne : (∫ y, f₀ y ∂μ₀) ≠ 0 := by
    rw [hint]
    have hpos : 0 < μ₀ S := hSo.isOpen.measure_pos μ₀ ⟨δ, hδS⟩
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' hSc.measure_lt_top.ne).ne'
  obtain ⟨hfin₀, _⟩ := conjugationAverage_integratedAction_trace ρ K μ₀ hρ A f₀
  have hscaled : (∫ y, f₀ y ∂μ₀) • T ∈ finiteRankEnd V :=
    conjugationAverage_integratedAction_of_eq ρ K μ₀ hρ.1 A f₀ hsupp T heq ▸ hfin₀
  have hfin : T ∈ finiteRankEnd V := by
    simpa only [inv_smul_smul₀ hne] using (finiteRankEnd V).smul_mem (∫ y, f₀ y ∂μ₀)⁻¹
      hscaled
  refine ⟨FiniteRankEnd.trace ⟨T, hfin⟩, fun μ _ => ⟨U, hU, hδ, ?_⟩⟩
  intro f hf
  obtain ⟨hfin', htrace⟩ := conjugationAverage_integratedAction_trace ρ K μ hρ A f
  let T' : finiteRankEnd V :=
    ⟨conjugationAverage ρ hρ.1 K (Hecke.integratedAction μ ρ hρ.1 f ∘ₗ A), hfin'⟩
  have hT' : T' = (∫ y, f y ∂μ) • (⟨T, hfin⟩ : finiteRankEnd V) :=
    Subtype.ext (conjugationAverage_integratedAction_of_eq ρ K μ hρ.1 A f hf T heq)
  calc
    twistedDistribution μ ρ hρ A f = FiniteRankEnd.trace T' := htrace.symm
    _ = _ := by rw [hT', map_smul, smul_eq_mul, mul_comm]

end LocalValue

end Langlands.BaseChange
