import Langlands.Global.AdelicUnipotentConstantTermDifferentiation
import Langlands.Global.AdelicUnipotentArchimedeanRepresentatives
import Langlands.Global.AdelicGroupPolish
import Langlands.Analysis.FamilyLIntegral

/-! # Deviation from a unipotent constant term for families of functions

For a family `g o` of continuous functions on `G(𝔸)`, indexed by an arbitrary measure space,
left invariant under `U(F)` and right invariant under an open finite level, the integral over the
family of `‖g o x - g_U o (x)‖` (with `g_U` the normalized constant term along a closed unipotent
subgroup `U`) is at most the supremum, over a fixed compact set `D` of archimedean points of `U`,
of the integrals of `‖g o x - g o (u x)‖`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj ENNReal

namespace Langlands.Global

open AdelicGroupPoints InfiniteAdelicGroupPoints Langlands.GroupScheme Langlands.Analysis

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  [LocallyOfFiniteType G.X.hom]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "V" => SubgroupFunctor.range j
local notation "H" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "ν₀" => AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
local notation "m" => map F U G j

/-- **Family oscillation along a unipotent constant term.** On a compact finite slice `Yf` and at
an open level `L` there is a compact set `D` of archimedean points of `U` such that, for every
family of continuous functions left invariant under `U(F)` and right invariant under `L`,
`∫ ‖g o x - (g o)_U(x)‖ ≤ sup_{v ∈ D} ∫ ‖g o x - g o (v x)‖` over an arbitrary measure space. -/
theorem adelicUnipotentFamilyOscillation [Smooth U.X.hom]
    (hconn : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (Yf : Set Gf) (hY : IsCompact Yf) (L : Subgroup Gf) (hL : IsOpen (L : Set Gf)) :
    ∃ D : Set U∞, IsCompact D ∧
      ∀ {Ω : Type w} [MeasurableSpace Ω] (mΩ : Measure Ω) (g : Ω → A → ℂ),
        (∀ o, Continuous (g o)) → Measurable (fun p : Ω × A => g p.1 p.2) →
        (∀ o (q : RationalGroupPoints F U) x, g o (m (rational F U q) * x) = g o x) →
        (∀ o, ∀ l ∈ L, ∀ x, g o (x * ofFinite F G l) = g o x) →
        ∀ x : A, finite F G x ∈ Yf →
          ∫⁻ o, ‖g o x - subgroupConstantTerm F j (g o) x‖ₑ ∂mΩ ≤
            ⨆ v ∈ D, ∫⁻ o, ‖g o x - g o (m (ofInfinite F U v) * x)‖ₑ ∂mΩ := by
  obtain ⟨D, hD, hrep⟩ := adelicUnipotentArchimedeanRepresentatives j hconn hu Yf hY L hL
  refine ⟨D, hD, ?_⟩
  intro Ω _ mΩ g hg hgm hgR hgL x hx
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
  have hm₀s : m₀ s ≠ (⊤ : ℝ≥0∞) := by
    change (c • mh) s ≠ ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G V)
      (hsFinite mh).ne
  have : IsFiniteMeasure (m₀.restrict s) := isFiniteMeasure_restrict.mpr hm₀s
  have hpres : MeasurePreserving (LeftCosetSpace.mk Γ) (m₀.restrict s) ν₀ := by
    simpa only [m₀, Measure.restrict_smul,
      AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure,
      AdelicSubgroupPoints.rationalQuotientHaarMeasure, LeftCosetSpace.haarQuotientMeasure, mh, c]
        using (hsPres mh).smul_measure c
  have hmass : (m₀.restrict s) univ = 1 := by
    have h := hpres.measure_preimage (s := univ) MeasurableSet.univ.nullMeasurableSet
    rw [preimage_univ] at h
    rw [h, measure_univ]
  -- the integrand on `H`
  let Fo : Ω → H → ℝ≥0∞ := fun o h => ‖g o x - g o (h.val * x)‖ₑ
  have hFo : Measurable (Function.uncurry Fo) := by
    have hmul : Measurable fun h : H => h.val * x :=
      (continuous_subtype_val.mul continuous_const).measurable
    exact ((hgm.comp (measurable_fst.prodMk (measurable_const : Measurable fun _ : Ω × H => x))).sub
      (hgm.comp (measurable_fst.prodMk (hmul.comp measurable_snd)))).enorm
  -- pointwise bound for each member of the family
  have hpt (o : Ω) : ‖g o x - subgroupConstantTerm F j (g o) x‖ₑ ≤ ∫⁻ h, Fo o h ∂(m₀.restrict s) := by
    let φ := LeftCosetSpace.lift Γ (fun y : H => g o (y.val * x)) (fun r y => by
      obtain ⟨r₀, hr₀⟩ := (mem_rationalSubgroup_range_iff j r.val).mp r.2
      change g o ((r.val.val * y.val) * x) = _
      rw [← hr₀, mul_assoc]
      exact hgR o r₀ (y.val * x))
    have hφ : Continuous φ :=
      (LeftCosetSpace.continuous_iff Γ).mpr ((hg o).comp (continuous_subtype_val.mul continuous_const))
    have ha : (fun q : Q => g o ((Quotient.out q : H).val * x)) = φ :=
      funext fun q => congrArg φ (Quotient.out_eq q)
    have hφi : Integrable φ ν₀ := hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hCT : subgroupConstantTerm F j (g o) x = ∫ q, φ q ∂ν₀ := by
      change (∫ q : Q, g o ((Quotient.out q : H).val * x) ∂ν₀) = _
      rw [ha]
    have hconst : (∫ _ : Q, g o x ∂ν₀) = g o x := by simp
    have hsub : g o x - subgroupConstantTerm F j (g o) x = ∫ q, (g o x - φ q) ∂ν₀ := by
      rw [hCT, integral_sub (integrable_const _) hφi, hconst]
    have hmeasQ : Measurable fun q : Q => ‖g o x - φ q‖ₑ :=
      (continuous_const.sub hφ).enorm.measurable
    rw [hsub]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    rw [← hpres.lintegral_comp hmeasQ]
    rfl
  -- a countable detecting set
  have : TopologicalSpace.SeparableSpace D := inferInstance
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense D
  let toH (v : U∞) : H := ⟨m (ofInfinite F U v), ⟨ofInfinite F U v, rfl⟩⟩
  have hrepH (h : H) : ∃ v ∈ D, ∀ o, g o (h.val * x) = g o (m (ofInfinite F U v) * x) := by
    obtain ⟨u₀, hu₀⟩ := AdelicSubgroupPoints.adelicRangeMap_surjective F j h
    obtain ⟨v, hv, q, hq⟩ := hrep u₀
    obtain ⟨l, hl⟩ := hq x hx
    refine ⟨v, hv, fun o => ?_⟩
    have he : m u₀ = h.val := congrArg Subtype.val hu₀
    rw [← he, ← hgR o q (m u₀ * x), hl, hgL o l.val l.property]
  have hzero : ∀ o, (∀ h ∈ (fun v : D => toH v.val) '' S, Fo o h = 0) → ∀ h, Fo o h = 0 := by
    intro o h0 h
    have hcont : Continuous fun v : D => Fo o (toH v.val) :=
      ((continuous_const.sub ((hg o).comp
        (((map F U G j).continuous.comp (ofInfinite F U).continuous).comp
          continuous_subtype_val |>.mul continuous_const))).enorm)
    have hclosed : IsClosed {v : D | Fo o (toH v.val) = 0} := isClosed_eq hcont continuous_const
    have hall : ∀ v : D, Fo o (toH v.val) = 0 := by
      intro v
      have hsub : S ⊆ {v : D | Fo o (toH v.val) = 0} := fun v hv => h0 _ ⟨v, hv, rfl⟩
      exact hclosed.closure_subset_iff.mpr hsub (hSd.closure_eq.symm ▸ mem_univ v)
    obtain ⟨v, hv, hgv⟩ := hrepH h
    change ‖g o x - g o (h.val * x)‖ₑ = 0
    rw [hgv o]
    exact hall ⟨v, hv⟩
  calc ∫⁻ o, ‖g o x - subgroupConstantTerm F j (g o) x‖ₑ ∂mΩ
      ≤ ∫⁻ o, ∫⁻ h, Fo o h ∂(m₀.restrict s) ∂mΩ := lintegral_mono hpt
    _ ≤ (m₀.restrict s) univ * ⨆ h, ∫⁻ o, Fo o h ∂mΩ :=
        lintegral_lintegral_le_mul_iSup mΩ (m₀.restrict s) hFo (hSc.image _) hzero
    _ = ⨆ h, ∫⁻ o, Fo o h ∂mΩ := by rw [hmass, one_mul]
    _ ≤ ⨆ v ∈ D, ∫⁻ o, ‖g o x - g o (m (ofInfinite F U v) * x)‖ₑ ∂mΩ := by
        refine iSup_le fun h => ?_
        obtain ⟨v, hv, hgv⟩ := hrepH h
        refine le_iSup₂_of_le (f := fun v (_ : v ∈ D) =>
          ∫⁻ o, ‖g o x - g o (m (ofInfinite F U v) * x)‖ₑ ∂mΩ) v hv (le_of_eq ?_)
        refine lintegral_congr fun o => ?_
        change ‖g o x - g o (h.val * x)‖ₑ = _
        rw [hgv o]

end Langlands.Global
