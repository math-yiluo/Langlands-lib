import Langlands.BaseChange.TwistedCharacter.OpenCoset

/-! # A character distribution on a translated open coset -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure Set Function HarmonicAnalysis _root_.Topology
open Hecke.TestFunction (pullback)
open scoped ENNReal NNReal

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space H]
  (i : G →* H) (hi : IsOpenEmbedding i) (s : H)

/-- The open subgroup embedded as its right coset by `s`. -/
def translatedCosetEmbedding (g : G) : H := i g * s

include hi in
omit [IsTopologicalGroup G] [T2Space H] in
/-- Translation identifies the open subgroup with an open coset. -/
theorem isOpenEmbedding_translatedCoset : IsOpenEmbedding (translatedCosetEmbedding i s) :=
  (Homeomorph.mulRight s).isOpenEmbedding.comp hi

/-- Restrict an ambient distribution to the translated coset and express it in the subgroup coordinates. -/
def translatedCosetDistribution (D : Distribution H) : Distribution G :=
  let hj := isOpenEmbedding_translatedCoset i hi s
  D.comp ((SchwartzBruhat.extendZero hj.isOpen_range).comp
    (pullback hj.isEmbedding.toHomeomorph.symm).toLinearMap)

omit [IsTopologicalGroup G] in
@[simp]
theorem translatedCosetDistribution_apply (D : Distribution H) (f : SchwartzBruhat G) :
    translatedCosetDistribution i hi s D f =
      D (extendAlongOpenEmbedding (isOpenEmbedding_translatedCoset i hi s) f) := rfl

omit [Group G] [Group H] [IsTopologicalGroup G] [IsTopologicalGroup H] in
private theorem extendAlongOpenEmbedding_pullback {j : G → H} (hj : IsOpenEmbedding j)
    (a : G ≃ₜ G) (b : H ≃ₜ H) (h : ∀ g, j (a g) = b (j g)) (f : SchwartzBruhat G) :
    extendAlongOpenEmbedding hj (pullback a f) = pullback b (extendAlongOpenEmbedding hj f) := by
  ext x
  by_cases hx : x ∈ range j
  · obtain ⟨g, rfl⟩ := hx
    rw [extendAlongOpenEmbedding_apply, Hecke.TestFunction.pullback_apply,
      Hecke.TestFunction.pullback_apply, ← h, extendAlongOpenEmbedding_apply]
  · have hbx : b x ∉ range j := by
      rintro ⟨g, hg⟩
      have he : j (a.symm g) = x := b.injective (by
        rw [← h, a.apply_symm_apply, hg])
      exact hx ⟨a.symm g, he⟩
    rw [Hecke.TestFunction.pullback_apply]
    unfold extendAlongOpenEmbedding
    rw [SchwartzBruhat.extendZero_apply_of_not_mem _ _ hx,
      SchwartzBruhat.extendZero_apply_of_not_mem _ _ hbx]

omit [IsTopologicalGroup G] in
/-- Ambient conjugation invariance yields the corresponding twisted invariance on the coset. -/
theorem translatedCosetDistribution_invariant (D : Distribution H) (a : G)
    (e : G ≃ₜ G) (he : ∀ x, translatedCosetEmbedding i s (e x) =
      Distribution.conjugationHomeomorph (i a) (translatedCosetEmbedding i s x))
    (hD : Distribution.pushforward (Distribution.conjugationHomeomorph (i a)) D = D) :
    Distribution.pushforward e (translatedCosetDistribution i hi s D) =
      translatedCosetDistribution i hi s D := by
  ext f
  rw [Distribution.pushforward_apply, translatedCosetDistribution_apply,
    extendAlongOpenEmbedding_pullback _ _ _ he, ← Distribution.pushforward_apply, hD,
    translatedCosetDistribution_apply]

section Haar

variable [LocallyCompactSpace G] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  (ν : Measure H) [ν.IsHaarMeasure]

include hi in
omit [T2Space H] [LocallyCompactSpace G] [LocallyCompactSpace H] [SecondCountableTopology H] in
/-- Left Haar measure in the subgroup coordinates of any right coset. -/
theorem isHaarMeasure_comap_translatedCoset : (ν.comap (translatedCosetEmbedding i s)).IsHaarMeasure := by
  let e := Homeomorph.mulRight s
  have h : ν.comap (translatedCosetEmbedding i s) = (ν.map e.symm).comap i := by
    change ν.comap (e ∘ i) = (ν.map e.symm).comap i
    rw [show ν.map e.symm = ν.comap e from e.toMeasurableEquiv.map_symm]
    exact (Measure.comap_comap (fun _ hA => hi.measurableEmbedding.measurableSet_image.mpr hA)
      e.injective (fun _ hA => e.toMeasurableEquiv.measurableEmbedding.measurableSet_image.mpr hA)
      ν).symm
  rw [h]
  let : (ν.map e.symm).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν s⁻¹
  exact IsHaarMeasure.comap (mH := inferInstance) _ hi

include hi in
omit [T2Space H] in
/-- If the open subgroup's Haar measure is right invariant, ambient right translation
by any subgroup element preserves Haar measure. -/
theorem measurePreserving_mulRight_of_openEmbedding
    (hG : (ν.comap i).IsMulRightInvariant) (a : G) :
    MeasurePreserving (Homeomorph.mulRight (i a)) ν ν := by
  let hme := hi.measurableEmbedding
  let A := range i
  let r := Homeomorph.mulRight (i a)
  let τ := ν.map r
  let μ := ν.comap i
  have : τ.IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν (i a)
  have : μ.IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) _ hi
  have hrA : r ⁻¹' A = A := by
    ext x
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g * a⁻¹, ?_⟩
      rw [map_mul, map_inv, hg]
      change x * i a * (i a)⁻¹ = x
      group
    · rintro ⟨g, rfl⟩
      exact ⟨g * a, map_mul i g a⟩
  have hcom : τ.comap i = μ := by
    apply hme.map_injective
    rw [hme.map_comap, hme.map_comap]
    change (ν.map r).restrict A = ν.restrict A
    rw [restrict_map r.continuous.measurable hi.isOpen_range.measurableSet, hrA]
    change (ν.restrict (range i)).map r = ν.restrict (range i)
    rw [← hme.map_comap, map_map r.continuous.measurable hme.measurable,
      show r ∘ i = i ∘ (Homeomorph.mulRight a) from (funext fun x => (map_mul i x a).symm),
      ← map_map hme.measurable (Homeomorph.mulRight a).continuous.measurable]
    let : μ.IsMulRightInvariant := hG
    rw [show μ.map (Homeomorph.mulRight a) = μ from map_mul_right_eq_self _ _]
  let c := haarScalarFactor τ ν
  have hτ : τ = c • ν := isMulLeftInvariant_eq_smul τ ν
  have hμ : μ = c • μ := calc
    μ = τ.comap i := hcom.symm
    _ = c • μ := by
      rw [hτ, ← Measure.coe_nnreal_smul, Measure.comap_smul, Measure.coe_nnreal_smul]
  have hc : c = 1 := by
    obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : G)
    have hpos : 0 < μ K := measure_pos_of_mem_nhds μ hK
    have h := congrArg (fun m : Measure G => m K) hμ
    rw [← Measure.coe_nnreal_smul, Measure.smul_apply, smul_eq_mul] at h
    have heq : (c : ℝ≥0∞) * μ K = 1 * μ K := by simpa only [one_mul] using h.symm
    exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos.ne' hKc.measure_ne_top).mp heq)
  refine ⟨r.continuous.measurable, ?_⟩
  change τ = ν
  rw [hτ, hc, one_smul]

variable [T2Space G] [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- Invariance of the restricted ordinary character under the translated action
of the subgroup. -/
def TranslatedCosetCharacterStatement (ν : Measure H) [IsFiniteMeasureOnCompacts ν]
    [ν.IsMulLeftInvariant] (π : Representation ℂ H W) (hπ : IsAdmissible π) : Prop :=
  (ν.comap i).IsMulRightInvariant → ∀ (a : G) (e : G ≃ₜ G),
    (∀ x, translatedCosetEmbedding i s (e x) =
      Distribution.conjugationHomeomorph (i a) (translatedCosetEmbedding i s x)) →
    Distribution.pushforward e (translatedCosetDistribution i hi s (Character.distribution ν π hπ)) =
      translatedCosetDistribution i hi s (Character.distribution ν π hπ)

omit [T2Space G] [TotallyDisconnectedSpace G] in
theorem translatedCosetCharacter (π : Representation ℂ H W) (hπ : IsAdmissible π) :
    TranslatedCosetCharacterStatement i hi s ν π hπ := by
  intro hG a e he
  apply translatedCosetDistribution_invariant i hi s _ a e he
  ext f
  rw [Distribution.pushforward_apply]
  apply Character.distribution_conjugation_of_measurePreserving
  change MeasurePreserving (fun x : H => i a * x * (i a)⁻¹) ν ν
  rw [← map_inv i a]
  exact (measurePreserving_mulRight_of_openEmbedding i hi ν hG a⁻¹).comp
    (measurePreserving_mul_left ν (i a))

end Haar

end Langlands.BaseChange
