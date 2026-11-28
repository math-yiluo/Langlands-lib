import Langlands.Global.AdelicUnipotentConstantTermDifferentiation
import Langlands.Global.AdelicGroupPolish
import Langlands.Analysis.FamilyLIntegral

/-! # Constant terms as integrals over a relatively compact fundamental domain

For a closed smooth connected unipotent subgroup `U` of `G`, there is a probability measure `ν'` on
the adelic points `U(𝔸)` (viewed in `G(𝔸)`), supported in a compact set, such that the normalized
constant term along `U` of every continuous left `U(F)`-invariant function `f` is
`∫ f(h x) dν'(h)`. The measure is the mass-normalized Haar measure restricted to a relatively
compact fundamental domain of `U(F)`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj ENNReal

namespace Langlands.Global

open AdelicGroupPoints Langlands.GroupScheme Langlands.Analysis

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "A" => AdelicGroupPoints F G
local notation "V" => SubgroupFunctor.range j
local notation "H" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "ν₀" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
local notation "m" => map F U G j

/-- **Fundamental-domain measure for a unipotent constant term.** There is a probability measure on
`U(𝔸)` concentrated on a compact set that represents the normalized constant term of every
continuous left `U(F)`-invariant function. -/
theorem exists_unipotentFundamentalMeasure [Smooth U.X.hom]
    (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U) :
    ∃ (ν : Measure H) (C : Set H), IsProbabilityMeasure ν ∧ IsCompact C ∧ ν Cᶜ = 0 ∧
      ∀ f : A → ℂ, Continuous f →
        (∀ (q : RationalGroupPoints F U) x, f (m (rational F U q) * x) = f x) →
        ∀ x, subgroupConstantTerm F j f x = ∫ h, f (h.val * x) ∂ν := by
  let : IsClosed (H : Set A) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace H := (show IsClosed (H : Set A) from inferInstance).locallyCompactSpace
  let : CompactSpace Q :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j inferInstance hconn hu
  let : BorelSpace Q := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let : IsProbabilityMeasure ν₀ :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  obtain ⟨K, hK, hKcov⟩ := EisensteinConstantTerm.exists_isCompact_mul_mem Γ
  obtain ⟨s, hs, hsc, _, _, hsPres, hsFinite, _⟩ := LeftCosetSpace.relativelyCompactFundamentalDomain
    Γ (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G V) K hK (by
      intro y
      obtain ⟨r, hr, y₀, hy₀, rfl⟩ := hKcov y
      exact ⟨⟨r⁻¹, Subgroup.inv_mem Γ hr⟩, by simpa using hy₀⟩)
  let mh : Measure H := Measure.haar
  let c := AdelicSubgroupPoints.quotientMassNormalizer F G V
  let m₀ : Measure H := c • mh
  have hpres : MeasurePreserving (LeftCosetSpace.mk Γ) (m₀.restrict s) ν₀ := by
    simpa only [m₀, Measure.restrict_smul,
      AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
      AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure, mh, c]
        using (hsPres mh).smul_measure c
  have hmass : (m₀.restrict s) univ = 1 := by
    have h := hpres.measure_preimage (s := univ) MeasurableSet.univ.nullMeasurableSet
    rw [preimage_univ] at h
    rw [h, measure_univ]
  refine ⟨m₀.restrict s, closure s, ⟨hmass⟩, hsc, ?_, ?_⟩
  · rw [Measure.restrict_apply' hs]
    exact measure_mono_null (fun z hz => hz.1 (subset_closure hz.2)) (measure_empty)
  · intro f hf hfR x
    let φ := LeftCosetSpace.lift Γ (fun y : H => f (y.val * x)) (fun r y => by
      obtain ⟨r₀, hr₀⟩ := (mem_rationalSubgroup_range_iff j r.val).mp r.2
      change f ((r.val.val * y.val) * x) = _
      rw [← hr₀, mul_assoc]
      exact hfR r₀ (y.val * x))
    have hφ : Continuous φ :=
      (LeftCosetSpace.continuous_iff Γ).mpr (hf.comp (continuous_subtype_val.mul continuous_const))
    have ha : (fun q : Q => f ((Quotient.out q : H).val * x)) = φ :=
      funext fun q => congrArg φ (Quotient.out_eq q)
    change (∫ q : Q, f ((Quotient.out q : H).val * x) ∂ν₀) = _
    rw [ha, ← hpres.map_eq, integral_map hpres.measurable.aemeasurable]
    · rfl
    · rw [hpres.map_eq]
      exact hφ.aestronglyMeasurable

/-- **Family bound for a unipotent constant term.** There is a compact set `C` of points of
`U(𝔸)` such that for every family of continuous left `U(F)`-invariant functions over an arbitrary
measure space, `∫ ‖(f o)_U(x)‖ ≤ sup_{h ∈ C} ∫ ‖f o (h x)‖`. -/
theorem exists_lintegral_enorm_subgroupConstantTerm_le [Smooth U.X.hom]
    (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U) :
    ∃ C : Set H, IsCompact C ∧
      ∀ {Ω : Type w} [MeasurableSpace Ω] (mΩ : Measure Ω) (f : Ω → A → ℂ),
        (∀ o, Continuous (f o)) → Measurable (fun p : Ω × A => f p.1 p.2) →
        (∀ o (q : RationalGroupPoints F U) x, f o (m (rational F U q) * x) = f o x) →
        ∀ x : A, ∫⁻ o, ‖subgroupConstantTerm F j (f o) x‖ₑ ∂mΩ ≤
          ⨆ h ∈ C, ∫⁻ o, ‖f o (h.val * x)‖ₑ ∂mΩ := by
  obtain ⟨ν, C, hν, hC, hνC, hrep⟩ := exists_unipotentFundamentalMeasure j hconn hu
  refine ⟨C, hC, ?_⟩
  intro Ω _ mΩ f hf hfm hfR x
  have hT : ∀ᵐ h ∂ν, h ∈ C := by
    rw [ae_iff]
    exact hνC
  have : TopologicalSpace.SeparableSpace C := inferInstance
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense C
  let Fo : Ω → H → ℝ≥0∞ := fun o h => ‖f o (h.val * x)‖ₑ
  have hFo : Measurable (Function.uncurry Fo) := by
    have hmul : Measurable fun h : H => h.val * x :=
      (continuous_subtype_val.mul continuous_const).measurable
    exact (hfm.comp (measurable_fst.prodMk (hmul.comp measurable_snd))).enorm
  have hzero : ∀ o, (∀ h ∈ (Subtype.val '' S : Set H), Fo o h = 0) → ∀ h ∈ C, Fo o h = 0 := by
    intro o h0 h hh
    have hcont : Continuous fun c : C => Fo o c.val :=
      ((hf o).comp ((continuous_subtype_val.comp continuous_subtype_val).mul continuous_const)).enorm
    have hclosed : IsClosed {c : C | Fo o c.val = 0} := isClosed_eq hcont continuous_const
    have hsub : S ⊆ {c : C | Fo o c.val = 0} := fun c hc => h0 _ ⟨c, hc, rfl⟩
    have hall : ∀ c : C, Fo o c.val = 0 := by
      intro c
      exact hclosed.closure_subset_iff.mpr hsub (hSd.closure_eq.symm ▸ mem_univ c)
    exact hall ⟨h, hh⟩
  have hpt (o : Ω) : ‖subgroupConstantTerm F j (f o) x‖ₑ ≤ ∫⁻ h, Fo o h ∂ν := by
    rw [hrep (f o) (hf o) (hfR o) x]
    exact enorm_integral_le_lintegral_enorm _
  calc ∫⁻ o, ‖subgroupConstantTerm F j (f o) x‖ₑ ∂mΩ
      ≤ ∫⁻ o, ∫⁻ h, Fo o h ∂ν ∂mΩ := lintegral_mono hpt
    _ ≤ ν univ * ⨆ h ∈ C, ∫⁻ o, Fo o h ∂mΩ :=
        lintegral_lintegral_le_mul_iSup_of_ae mΩ ν hFo
          (by rintro _ ⟨c, -, rfl⟩; exact c.property) (hSc.image _) hT hzero
    _ = ⨆ h ∈ C, ∫⁻ o, ‖f o (h.val * x)‖ₑ ∂mΩ := by rw [measure_univ, one_mul]

end Langlands.Global
