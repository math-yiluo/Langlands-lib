import Langlands.BaseChange.CharacterFunction
import Langlands.HarmonicAnalysis.Distribution.Subspace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Restricting character functions to a coset of an open subgroup -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory Topology
open scoped ENNReal NNReal

universe uG uH uV

variable {G : Type uG} [TopologicalSpace G] {H : Type uH} [TopologicalSpace H]

section TestFunctions

variable [T2Space H]

/-- Transport a test function along an open embedding and extend by zero. -/
def extendAlongOpenEmbedding {j : G → H} (hj : IsOpenEmbedding j)
    (f : SchwartzBruhat G) : SchwartzBruhat H :=
  SchwartzBruhat.extendZero hj.isOpen_range
    (Hecke.TestFunction.pullback hj.isEmbedding.toHomeomorph.symm f)

@[simp]
theorem extendAlongOpenEmbedding_apply {j : G → H} (hj : IsOpenEmbedding j)
    (f : SchwartzBruhat G) (g : G) : extendAlongOpenEmbedding hj f (j g) = f g := by
  change SchwartzBruhat.extendZero hj.isOpen_range
    (Hecke.TestFunction.pullback hj.isEmbedding.toHomeomorph.symm f)
    (hj.isEmbedding.toHomeomorph g).val = f g
  rw [SchwartzBruhat.extendZero_apply_subtype, Hecke.TestFunction.pullback_apply,
    Homeomorph.symm_apply_apply]

private theorem integral_extendAlongOpenEmbedding [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace H] [BorelSpace H] {j : G → H} (hj : IsOpenEmbedding j)
    (ν : Measure H) (f : SchwartzBruhat G) (q : H → ℂ) :
    (∫ z, extendAlongOpenEmbedding hj f z * q z ∂ν) =
      ∫ g, f g * q (j g) ∂(ν.comap j) := by
  have he := hj.measurableEmbedding
  calc
    _ = ∫ z in Set.range j, extendAlongOpenEmbedding hj f z * q z ∂ν := by
      rw [← integral_indicator hj.isOpen_range.measurableSet]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ Set.range j
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        simp [extendAlongOpenEmbedding, hz]
    _ = _ := by rw [← he.map_comap, he.integral_map]; simp only [extendAlongOpenEmbedding_apply]

end TestFunctions

variable [Group G] [Group H] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Admissibility on an open embedded subgroup implies admissibility on the ambient group. -/
theorem isAdmissible_of_comp_openEmbedding (i : G →* H) (hi : IsOpenEmbedding i)
    (π : Representation ℂ H V) (hπ : IsAdmissible (π.comp i)) : IsAdmissible π := by
  refine ⟨?_, ?_⟩
  · intro v
    obtain ⟨K, hK⟩ := hπ.1 v
    let K' : OpenSubgroup H := ⟨K.toSubgroup.map i, hi.isOpenMap _ K.isOpen⟩
    refine ⟨K', fun k => ?_⟩
    obtain ⟨g, hg, h⟩ := Subgroup.mem_map.mp k.property
    change π (k : H) v = v
    rw [← h]
    exact hK ⟨g, hg⟩
  · intro K
    let K' := K.comap i hi.continuous
    have _ : Module.Finite ℂ (fixedVectors (π.comp i) K'.toSubgroup) := hπ.2 K'
    have hle : fixedVectors π K.toSubgroup ≤ fixedVectors (π.comp i) K'.toSubgroup :=
      fun _ hv k => hv ⟨i k, k.property⟩
    exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

variable [IsTopologicalGroup G] [IsTopologicalGroup H]
  [LocallyCompactSpace G] [LocallyCompactSpace H] [SecondCountableTopology G]

private theorem exists_haar_comap_rightCoset [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace H] [BorelSpace H] (i : G →* H) (hi : IsOpenEmbedding i) (t : H)
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ ν : Measure H, ν.IsHaarMeasure ∧ ν.comap (fun g => i g * t) = μ := by
  let j := fun g => i g * t
  let ν₀ : Measure H := Measure.haar
  let e := Homeomorph.mulRight t
  have heq : ν₀.comap j = (ν₀.map e.symm).comap i := by
    change ν₀.comap (e ∘ i) = (ν₀.map e.symm).comap i
    rw [show ν₀.map e.symm = ν₀.comap e from e.toMeasurableEquiv.map_symm]
    exact (Measure.comap_comap (fun _ hs => hi.measurableEmbedding.measurableSet_image.mpr hs)
      e.injective (fun _ hs => e.toMeasurableEquiv.measurableEmbedding.measurableSet_image.mpr hs)
      ν₀).symm
  have _ : (ν₀.map e.symm).IsHaarMeasure :=
    Measure.isHaarMeasure_map_mul_right ν₀ t⁻¹
  have _ : (ν₀.comap j).IsHaarMeasure := by
    rw [heq]
    exact Measure.IsHaarMeasure.comap (mH := inferInstance) _ hi
  let c := Measure.haarScalarFactor μ (ν₀.comap j)
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ (ν₀.comap j)).ne'
  refine ⟨(c : ℝ≥0∞) • ν₀, Measure.IsHaarMeasure.smul ν₀ (by exact_mod_cast hc)
    ENNReal.coe_ne_top, ?_⟩
  rw [Measure.comap_smul, Measure.coe_nnreal_smul]
  exact (Measure.isMulLeftInvariant_eq_smul μ (ν₀.comap j)).symm

variable [T2Space G] [TotallyDisconnectedSpace G] [T2Space H] [TotallyDisconnectedSpace H]

/-- An ordinary character function on the ambient group restricts on the right coset
`g ↦ i(g)t` to the twisted character function with twisting endomorphism `π(t)`. -/
theorem IsCharacterFunction.twisted_of_openEmbedding (i : G →* H) (hi : IsOpenEmbedding i)
    (π : Representation ℂ H V) (hπ : IsAdmissible π) (hρ : IsAdmissible (π.comp i))
    {Θ : H → ℂ} (hΘ : IsCharacterFunction π hπ Θ) (t : H) :
    IsTwistedCharacterFunction (π.comp i) hρ (π t) (fun g => Θ (i g * t)) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  let _ : MeasurableSpace H := borel H
  have _ : BorelSpace H := ⟨rfl⟩
  intro μ _
  let j := fun g => i g * t
  have hj : IsOpenEmbedding j := (Homeomorph.mulRight t).isOpenEmbedding.comp hi
  obtain ⟨ν, hν, hμ⟩ := exists_haar_comap_rightCoset i hi t μ
  let _ := hν
  obtain ⟨hli, htr⟩ := hΘ ν
  have hmap : μ.map j = ν.restrict (Set.range j) := by
    rw [← hμ, hj.measurableEmbedding.map_comap]
  refine ⟨?_, fun f => ?_⟩
  · intro g
    obtain ⟨s, hs, hint⟩ := hli (j g)
    refine ⟨j ⁻¹' s, hj.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    apply hj.measurableEmbedding.integrableOn_map_iff.mp
    exact hint.mono_measure (hmap ▸ Measure.restrict_le_self)
  · let f' := extendAlongOpenEmbedding hj f
    have hchange (q : H → ℂ) :
        (∫ z, f' z * q z ∂ν) = ∫ g, f g * q (j g) ∂μ := by
      rw [← hμ]
      exact integral_extendAlongOpenEmbedding hj ν f q
    have hact : Hecke.integratedAction ν π hπ.1 f' =
        Hecke.integratedAction μ (π.comp i) hρ.1 f ∘ₗ π t := by
      apply LinearMap.ext
      intro v
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
      intro a
      rw [map_sub, sub_eq_zero, LinearMap.comp_apply, Hecke.integratedAction_dual,
        Hecke.integratedAction_dual, hchange]
      simp [j, map_mul, Module.End.mul_apply]
    calc
      twistedDistribution μ (π.comp i) hρ (π t) f = Character.distribution ν π hπ f' := by
        rw [twistedDistribution_apply, Character.distribution_apply]
        exact congrArg FiniteRankEnd.trace (Subtype.ext hact.symm)
      _ = _ := (htr f').trans (hchange Θ)

end Langlands.BaseChange
