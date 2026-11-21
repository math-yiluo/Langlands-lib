import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical
import Mathlib.Algebra.Ring.AddAut
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Additive coordinates for Haar measure of a compact group of units -/

noncomputable section

namespace Langlands.BaseChange

open Function MeasureTheory Measure Topology Set HarishChandraSchwartz
open scoped ENNReal NNReal

universe u v w z

section Units

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
  [MeasurableSpace A] [BorelSpace A]

/-- Probability Haar measure on a compact group embedded openly in the underlying ring of
its unit representation is normalized additive Haar restricted to the image. -/
theorem map_normalizedHaar_eq_restrict_of_units (i : H →* Aˣ)
    (hi : IsOpenEmbedding (fun h => (i h : A))) (μ : Measure A) [μ.IsAddHaarMeasure] :
    Measure.map (fun h => (i h : A)) (normalizedHaar H) =
      (μ (range fun h => (i h : A)))⁻¹ • μ.restrict (range fun h => (i h : A)) := by
  let a : H → A := fun h => (i h : A)
  have ha : IsOpenEmbedding a := hi
  have hemb := ha.measurableEmbedding
  have hcompact : IsCompact (range a) := isCompact_range ha.continuous
  have hne : μ (range a) ≠ 0 := (ha.isOpen_range.measure_pos μ ⟨a 1, mem_range_self 1⟩).ne'
  have hfin : μ (range a) ≠ ∞ := hcompact.measure_ne_top
  let ρ := μ.comap a
  have hρ : ρ univ = μ (range a) := by
    change μ.comap a univ = μ (range a)
    rw [hemb.comap_apply, image_univ]
  have : IsFiniteMeasure ρ := ⟨hρ ▸ hcompact.measure_lt_top⟩
  have : ρ.IsMulLeftInvariant := by
    constructor
    intro h
    let e : A ≃ₜ+ A :=
      { toAddEquiv := Multiplicative.toAdd (AddAut.mulLeft (i h))
        continuous_toFun := continuous_const.mul continuous_id
        continuous_invFun := continuous_const.mul continuous_id }
    have he (x : H) : e (a x) = a (h * x) := by
      change (i h : A) * (i x : A) = (i (h * x) : A)
      rw [map_mul, Units.val_mul]
    have hpre (s : Set H) : e ⁻¹' (a '' s) = a '' ((h * ·) ⁻¹' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        refine ⟨h⁻¹ * y, ?_, e.injective ?_⟩
        · simpa using hy
        · simpa only [he, mul_inv_cancel_left] using hyx
      · rintro ⟨y, hy, rfl⟩
        exact ⟨h * y, hy, (he y).symm⟩
    have hrange : e ⁻¹' range a = range a := by
      simpa only [image_univ, preimage_univ] using hpre univ
    have hemeas : Measurable (e : A → A) := e.continuous.measurable
    have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
    have hscale := isAddLeftInvariant_eq_smul (μ.map e) μ
    have hfactor : addHaarScalarFactor (μ.map e) μ = 1 := by
      have hm := congrArg (fun ν : Measure A => ν (range a)) hscale
      rw [map_apply hemeas ha.isOpen_range.measurableSet, hrange, Measure.smul_apply] at hm
      change μ (range a) = (addHaarScalarFactor (μ.map e) μ : ℝ≥0∞) * μ (range a) at hm
      apply ENNReal.coe_injective
      change (addHaarScalarFactor (μ.map e) μ : ℝ≥0∞) = 1
      apply (ENNReal.mul_left_inj hne hfin).mp
      simpa only [one_mul] using hm.symm
    have hmap : μ.map e = μ := by rw [hscale, hfactor, one_smul]
    ext1 s hs
    change (μ.comap a).map (h * ·) s = (μ.comap a) s
    rw [map_apply (measurable_const_mul h) hs, hemb.comap_apply, hemb.comap_apply,
      ← hpre, ← map_apply hemeas (hemb.measurableSet_image.2 hs), hmap]
  have : SecondCountableTopology H := ha.isEmbedding.secondCountableTopology
  have : T2Space H := ha.isEmbedding.t2Space
  have hhaar : ρ = μ (range a) • normalizedHaar H := by
    simpa only [TopologicalSpace.PositiveCompacts.coe_top, normalizedHaar, hρ]
      using haarMeasure_unique ρ ⊤
  have hn : normalizedHaar H = (μ (range a))⁻¹ • ρ := by
    rw [hhaar, smul_smul, ENNReal.inv_mul_cancel hne hfin, one_smul]
  change Measure.map a (normalizedHaar H) = _
  rw [hn, Measure.map_smul _ hemb.measurable.aemeasurable, hemb.map_comap]

/-- The image of the compact group has an additive Haar density that is constant on its
range and zero outside. Its topological support is exactly the range. -/
theorem exists_normalizedHaar_chartDensity (i : H →* Aˣ)
    (hi : IsOpenEmbedding (fun h => (i h : A))) (μ : Measure A) [μ.IsAddHaarMeasure] :
    ∃ f : LocallyConstant A ℝ≥0, HasCompactSupport (f : A → ℝ≥0) ∧
      tsupport (f : A → ℝ≥0) = range (fun h => (i h : A)) ∧
      Measure.map (fun h => (i h : A)) (normalizedHaar H) =
        μ.withDensity (fun x => (f x : ℝ≥0∞)) := by
  let S := range (fun h => (i h : A))
  have hS : IsCompact S := isCompact_range hi.continuous
  have hc : IsClopen S := ⟨hS.isClosed, hi.isOpen_range⟩
  have hne : μ S ≠ 0 := (hc.isOpen.measure_pos μ ⟨(i 1 : A), mem_range_self 1⟩).ne'
  have hfin : μ S ≠ ∞ := hS.measure_ne_top
  let c : ℝ≥0 := (μ S)⁻¹.toNNReal
  have hcoe : (c : ℝ≥0∞) = (μ S)⁻¹ := ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hne)
  have hc0 : c ≠ 0 := by
    intro hz
    exact ENNReal.inv_ne_zero.mpr hfin (by simpa [hz] using hcoe.symm)
  let f := (LocallyConstant.const A c).indicator hc
  have hsupp : Function.support (f : A → ℝ≥0) = S := by
    ext x
    by_cases hx : x ∈ S <;> simp [f, hx, Function.mem_support, hc0]
  have htsupp : tsupport (f : A → ℝ≥0) = S := by rw [tsupport, hsupp, hc.isClosed.closure_eq]
  have hfcompact : HasCompactSupport (f : A → ℝ≥0) := by
    change IsCompact (tsupport (f : A → ℝ≥0))
    rw [htsupp]
    exact hS
  refine ⟨f, hfcompact, htsupp, ?_⟩
  have hf : (fun x => (f x : ℝ≥0∞)) = S.indicator (fun _ => (μ S)⁻¹) := by
    funext x
    by_cases hx : x ∈ S <;> simp [f, hx, hcoe]
  rw [map_normalizedHaar_eq_restrict_of_units i hi μ, hf,
    withDensity_indicator hc.isClosed.measurableSet, withDensity_const]

end Units

section Prod

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
  [MeasurableSpace A] [BorelSpace A]
  {J : Type w} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
  {B : Type z} [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B]
  [MeasurableSpace B] [BorelSpace B]

/-- The two probability Haar measures in compact averaging give a single compactly
supported locally constant density in product additive coordinates. -/
theorem exists_normalizedHaar_prod_chartDensity (i : H →* Aˣ) (j : J →* Bˣ)
    (hi : IsOpenEmbedding (fun h => (i h : A))) (hj : IsOpenEmbedding (fun k => (j k : B)))
    (μ : Measure (A × B)) [μ.IsAddHaarMeasure] :
    ∃ f : LocallyConstant (A × B) ℝ≥0, HasCompactSupport (f : A × B → ℝ≥0) ∧
      tsupport (f : A × B → ℝ≥0) = range (Prod.map (fun h => (i h : A)) (fun k => (j k : B))) ∧
      Measure.map (Prod.map (fun h => (i h : A)) (fun k => (j k : B)))
        ((normalizedHaar H).prod (normalizedHaar J)) =
        μ.withDensity (fun x => (f x : ℝ≥0∞)) := by
  have : SecondCountableTopology H := hi.isEmbedding.secondCountableTopology
  have : SecondCountableTopology J := hj.isEmbedding.secondCountableTopology
  have : T2Space H := hi.isEmbedding.t2Space
  have : T2Space J := hj.isEmbedding.t2Space
  have hprob : normalizedHaar (H × J) = (normalizedHaar H).prod (normalizedHaar J) := by
    apply (haarMeasure_eq_iff ⊤ _).2
    rw [TopologicalSpace.PositiveCompacts.coe_top, measure_univ]
  let e := MulEquiv.prodUnits.symm.toMonoidHom.comp (i.prodMap j)
  rw [← hprob]
  exact exists_normalizedHaar_chartDensity e (hi.prodMap hj) μ

end Prod

/-- Open embeddings of compact groups into additive ring coordinates turn their product
probability Haar measure into additive Haar with a compactly supported locally constant
density. -/
def CompactOpenHaarChartStatement : Prop :=
  ∀ {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
    {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A]
    {J : Type w} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
    {B : Type z} [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B]
    [MeasurableSpace B] [BorelSpace B]
    (i : H →* Aˣ) (j : J →* Bˣ),
    IsOpenEmbedding (fun h => (i h : A)) →
    IsOpenEmbedding (fun k => (j k : B)) →
    ∀ (μ : Measure (A × B)) [μ.IsAddHaarMeasure],
      ∃ f : LocallyConstant (A × B) ℝ≥0, HasCompactSupport (f : A × B → ℝ≥0) ∧
        tsupport (f : A × B → ℝ≥0) =
          range (Prod.map (fun h => (i h : A)) (fun k => (j k : B))) ∧
        Measure.map (Prod.map (fun h => (i h : A)) (fun k => (j k : B)))
          ((normalizedHaar H).prod (normalizedHaar J)) =
          μ.withDensity (fun x => (f x : ℝ≥0∞))

theorem compactOpenHaarChart : CompactOpenHaarChartStatement.{u, v, w, z} := by
  intro H _ _ _ _ _ _ A _ _ _ _ _ _ _ _ J _ _ _ _ _ _ B _ _ _ _ _ _ _ _ i j hi hj μ _
  exact exists_normalizedHaar_prod_chartDensity i j hi hj μ

end Langlands.BaseChange
