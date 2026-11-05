import Langlands.Analysis.Local.CompactOpenIndexHaarStatement

noncomputable section

universe u

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands.Haar

variable {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
/-- An open subgroup of a compact group has finite relative index. -/
theorem finiteIndex_subgroupOf_compact_open
    (K J : Subgroup G) (hKc : IsCompact (K : Set G))
    (hJo : IsOpen (J : Set G)) :
    (J.subgroupOf K).FiniteIndex := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hJo' : IsOpen (J.subgroupOf K : Set K) :=
    hJo.preimage continuous_subtype_val
  let : DiscreteTopology (K ⧸ J.subgroupOf K) :=
    QuotientGroup.discreteTopology hJo'
  let : Finite (K ⧸ J.subgroupOf K) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Haar mass of a finite-index subgroup inside a compact open subgroup. -/
theorem relIndex_mul_measure (μ : Measure G) [IsMulLeftInvariant μ]
    (K J : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (hJo : IsOpen (J : Set G)) (hJK : J ≤ K) :
    (J.relIndex K : ℝ≥0∞) * μ J = μ K := by
  let ν : Measure K := μ.comap K.subtype
  have he : MeasurableEmbedding K.subtype :=
    hKo.isOpenEmbedding_subtypeVal.measurableEmbedding
  have : ν.IsMulLeftInvariant := IsMulLeftInvariant.comap μ he
  have : (J.subgroupOf K).FiniteIndex :=
    finiteIndex_subgroupOf_compact_open K J hKc hJo
  have hJo' : MeasurableSet (J.subgroupOf K : Set K) :=
    (hJo.preimage continuous_subtype_val).measurableSet
  have hJimage : K.subtype '' (J.subgroupOf K : Set K) = (J : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hJK hx⟩, hx, rfl⟩
  have hKimage : K.subtype '' (Set.univ : Set K) = (K : Set G) := by
    ext x
    simp
  have h := (J.subgroupOf K).index_mul_measure hJo' ν
  simpa only [ν, he.comap_apply, hJimage, hKimage, Subgroup.relIndex] using h

variable [LocallyCompactSpace G]

/-- Relative-index comparison determines the continuous-automorphism character. -/
theorem compactOpenIndexHaar : CompactOpenIndexHaarStatement.{u} := by
  intro G _ _ _ _ _ _ α K J hKc hKo hJo hJK hαJK
  let μ : Measure G := haar
  let Jα := J.map α.toMonoidHom
  have hJαo : IsOpen (Jα : Set G) :=
    α.toHomeomorph.isOpenMap _ hJo
  have hmass := relIndex_mul_measure μ K J hKc hKo hJo hJK
  have hmassα := relIndex_mul_measure μ K Jα hKc hKo hJαo hαJK
  have hscale : (mulEquivHaarChar α : ℝ≥0∞) * μ J = μ Jα := by
    have h := congrArg (fun ν : Measure G => ν (J : Set G))
      (mulEquivHaarChar_smul_eq_comap μ α)
    rw [show (⇑α : G → G) = ⇑α.toHomeomorph.toMeasurableEquiv from rfl] at h
    calc
      _ = (μ.comap α.toMeasurableEquiv) (J : Set G) := by
        simpa only [Measure.smul_apply, nnreal_smul_coe_apply] using h
      _ = μ (α.toMeasurableEquiv '' (J : Set G)) :=
        α.toMeasurableEquiv.measurableEmbedding.comap_apply _ _
      _ = μ Jα := rfl
  have hJ0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have hJtop : μ J ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono hJK) hKc.measure_lt_top).ne
  have heq : (mulEquivHaarChar α : ℝ≥0∞) * (Jα.relIndex K : ℝ≥0∞) =
      (J.relIndex K : ℝ≥0∞) := by
    apply (ENNReal.mul_left_inj hJ0 hJtop).mp
    calc
      ((mulEquivHaarChar α : ℝ≥0∞) * (Jα.relIndex K : ℝ≥0∞)) * μ J =
          (Jα.relIndex K : ℝ≥0∞) * ((mulEquivHaarChar α : ℝ≥0∞) * μ J) := by
            ac_rfl
      _ = (J.relIndex K : ℝ≥0∞) * μ J := by
        rw [hscale, hmassα, hmass]
  have heq' : mulEquivHaarChar α * (Jα.relIndex K : ℝ≥0) =
      (J.relIndex K : ℝ≥0) := by
    exact_mod_cast heq
  refine ⟨heq', ?_⟩
  constructor
  · intro h
    rw [h, one_mul] at heq'
    exact_mod_cast heq'
  · intro h
    have : (J.subgroupOf K).FiniteIndex :=
      finiteIndex_subgroupOf_compact_open K J hKc hJo
    have hn : (J.relIndex K : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := J.subgroupOf K))
    rw [h] at heq'
    exact (mul_eq_right₀ hn).mp heq'

end Langlands.Haar
