import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.Local.QuotientNormalizingFunction
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Unfolding the integral of the diagonal of the twisted kernel

Let `G` be a locally compact, second countable Hausdorff group with a left Haar measure `μG`, `Γ` a
discrete subgroup with a compatible measure `ν` on `Γ \ G` (`IsCompatible Γ μG Measure.count ν`),
`θ` a continuous endomorphism of `G` with `θ Γ ⊆ Γ`, and `f ∈ C_c(G, ℂ)`. The diagonal of the
twisted kernel is `K(x, x) = ∑' γ : Γ, f (x⁻¹ γ θ x)` (`twistedKernelDiagonal`). If every `x` with a
nonvanishing term lies in `Γ · C` for a compact `C`, and `r i` represent, without repetition, the
`Γ`-`θ`-conjugacy classes of `Γ` that meet the `θ`-twisted conjugates of the support of `f`, then

`∫_{Γ \ G} K(x, x) dν(x) = ∑ i, ∫_{(Γ ∩ C_{r i}) \ G} f (x⁻¹ r i θ x) dν_i(x)`,

an unconditionally convergent sum of absolutely convergent integrals
(`twistedGeometricSide_unfolding`). The support condition holds whenever `Γ \ G` is compact
(`exists_isCompact_twistedSupport_of_compactSpace`, `twistedGeometricSide_unfolding_of_compactSpace`).

Getz–Hahn, *An introduction to automorphic representations* (2024), §18.5; Deligne–Kazhdan–Vignéras
(1984), A.1.c–d for `θ = id`.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Set Filter Topology
open Langlands.QuotientIntegration
open scoped ENNReal NNReal CompactlySupported

universe u

section Algebra

variable {G : Type u} [Group G] {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]

/-- `x ↦ f (x⁻¹ * δ * θ x)` is invariant under left multiplication by any subgroup `H` of the
twisted centralizer of `δ`; this is the invariance by which it descends to `H \ G`. -/
theorem apply_twistedConj_left_mul_of_le {H : Subgroup G} {θ : Θ} {δ : G}
    (hH : H ≤ twistedCentralizer θ δ) {A : Sort*} (f : G → A) (c : H) (x : G) :
    f ((c.val * x)⁻¹ * δ * θ (c.val * x)) = f (x⁻¹ * δ * θ x) :=
  congrArg f (twistedConj_left_mul θ δ ⟨c.val, hH c.property⟩ x)

/-- `γ ↦ g⁻¹ γ θ g` as a permutation of `Γ`, for `g ∈ Γ` and `θ Γ ⊆ Γ`. -/
private def twistedConjEquiv (Γ : Subgroup G) (θ : Θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (g : Γ) :
    Γ ≃ Γ :=
  (Equiv.mulLeft g⁻¹).trans (Equiv.mulRight ⟨θ g, hθΓ _ g.2⟩)

private theorem twistedConjEquiv_apply (Γ : Subgroup G) (θ : Θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ)
    (g δ : Γ) (y : G) :
    y⁻¹ * (twistedConjEquiv Γ θ hθΓ g δ : G) * θ y =
      ((g : G) * y)⁻¹ * δ * θ ((g : G) * y) := by
  simp [twistedConjEquiv, mul_assoc]

/-- Sums over `Γ` of a function of `x⁻¹ γ θ x` are left `Γ`-invariant in `x`. -/
private theorem tsum_twistedConj_left_mul {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (Γ : Subgroup G) (θ : Θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (F : G → M) (g : Γ) (x : G) :
    ∑' γ : Γ, F (((g : G) * x)⁻¹ * γ * θ ((g : G) * x)) = ∑' γ : Γ, F (x⁻¹ * γ * θ x) := by
  rw [← (twistedConjEquiv Γ θ hθΓ g).tsum_eq (fun γ : Γ => F (x⁻¹ * γ * θ x))]
  simp only [twistedConjEquiv_apply]

/-- The classes of `Γ ⊓ C_δ` and the class of `δ`: for a choice `d c ∈ Γ` with
`(d c)⁻¹ δ θ (d c) = c` for every `c` twisted conjugate to `δ` under `Γ`, the map
`(η, c) ↦ (d c)⁻¹ η` is a bijection `(Γ ⊓ C_δ) × class(δ) → Γ`. -/
private theorem bijective_classMap (Γ : Subgroup G) (θ : Θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) {δ : G}
    (hδ : δ ∈ Γ) (d : {γ : Γ // IsTwistedConjugate Γ θ δ γ} → Γ)
    (hd : ∀ c, ((d c : G))⁻¹ * δ * θ (d c : G) = c.1) :
    Function.Bijective (fun p : (Γ ⊓ twistedCentralizer θ δ : Subgroup G) ×
        {γ : Γ // IsTwistedConjugate Γ θ δ γ} =>
      (⟨((d p.2 : G))⁻¹ * p.1, Γ.mul_mem (Γ.inv_mem (d p.2).2)
        (Subgroup.mem_inf.1 p.1.2).1⟩ : Γ)) := by
  have key : ∀ (η : G), η ∈ twistedCentralizer θ δ →
      ∀ c : {γ : Γ // IsTwistedConjugate Γ θ δ γ},
      ((d c : G)⁻¹ * η) * δ * (θ ((d c : G)⁻¹ * η))⁻¹ = c.1 := by
    intro η hη c
    have hη' : η * δ * (θ η)⁻¹ = δ := by
      have h := (mem_twistedCentralizer θ δ η).1 hη
      calc η * δ * (θ η)⁻¹ = η * (η⁻¹ * δ * θ η) * (θ η)⁻¹ := by rw [h]
        _ = δ := by group
    rw [← hd c, map_mul, map_inv]
    calc (d c : G)⁻¹ * η * δ * ((θ (d c : G))⁻¹ * θ η)⁻¹
        = (d c : G)⁻¹ * (η * δ * (θ η)⁻¹) * θ (d c : G) := by group
      _ = (d c : G)⁻¹ * δ * θ (d c : G) := by rw [hη']
  constructor
  · rintro ⟨η₁, c₁⟩ ⟨η₂, c₂⟩ h
    have h' : ((d c₁ : G))⁻¹ * η₁ = ((d c₂ : G))⁻¹ * η₂ := congrArg Subtype.val h
    have hc : c₁ = c₂ := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← key η₁ (Subgroup.mem_inf.1 η₁.2).2 c₁, ← key η₂ (Subgroup.mem_inf.1 η₂.2).2 c₂, h']
    subst hc
    have hη : (η₁ : G) = η₂ := mul_left_cancel h'
    exact Prod.ext (Subtype.ext hη) rfl
  · intro γ
    have hmem : (γ : G) * δ * (θ γ)⁻¹ ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem γ.2 hδ) (Γ.inv_mem (hθΓ _ γ.2))
    let c : {γ : Γ // IsTwistedConjugate Γ θ δ γ} :=
      ⟨⟨(γ : G) * δ * (θ γ)⁻¹, hmem⟩, (γ : G)⁻¹, Γ.inv_mem γ.2, by simp [map_inv]⟩
    have hcent : (d c : G) * γ ∈ twistedCentralizer θ δ := by
      rw [mem_twistedCentralizer, map_mul]
      have hdc := hd c
      calc ((d c : G) * γ)⁻¹ * δ * (θ (d c : G) * θ γ)
          = (γ : G)⁻¹ * ((d c : G)⁻¹ * δ * θ (d c : G)) * θ γ := by group
        _ = δ := by
          rw [hdc]
          show (γ : G)⁻¹ * ((γ : G) * δ * (θ (γ : G))⁻¹) * θ (γ : G) = δ
          group
    refine ⟨(⟨(d c : G) * γ, Subgroup.mem_inf.2 ⟨Γ.mul_mem (d c).2 γ.2, hcent⟩⟩, c), ?_⟩
    apply Subtype.ext
    simp

end Algebra

section Topology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]

omit [MonoidHomClass Θ G G] in
/-- If `Γ \ G` is compact, every element of `G` is `g * y` with `g ∈ Γ` and `y` in a fixed compact
set, so the support hypothesis of `twistedGeometricSide_unfolding` holds for every `f`. -/
theorem exists_isCompact_twistedSupport_of_compactSpace [LocallyCompactSpace G]
    (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) [CompactSpace (LeftQuotient Γ)] (θ : Θ)
    (f : G → ℂ) :
    ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y := by
  obtain ⟨C, hC, hCK⟩ := leftQuotient_exists_isCompact_image Γ hΓ isCompact_univ
  refine ⟨C, hC, fun x _ _ _ => ?_⟩
  obtain ⟨y, hy, hyx⟩ := (hCK.symm ▸ Set.mem_univ (leftQuotientMap Γ x) :
    leftQuotientMap Γ x ∈ leftQuotientMap Γ '' C)
  have h : x * y⁻¹ ∈ Γ := QuotientGroup.rightRel_apply.mp (Quotient.exact hyx)
  exact ⟨x * y⁻¹, h, y, hy, by group⟩

variable [T2Space G]

omit [MonoidHomClass Θ G G] in
/-- For a compact `C`, only finitely many `γ ∈ Γ` have `f (y⁻¹ γ θ y) ≠ 0` for some `y ∈ C`. -/
private theorem finite_twistedSupport (Γ : Subgroup G) [DiscreteTopology Γ] (θ : Θ)
    (hθ : Continuous θ) (f : C_c(G, ℂ)) {C : Set G} (hC : IsCompact C) :
    {γ : Γ | ∃ y ∈ C, f (y⁻¹ * γ * θ y) ≠ 0}.Finite := by
  have hK : IsCompact ((fun p : G × G => p.1 * p.2 * (θ p.1)⁻¹) '' (C ×ˢ tsupport f)) :=
    (hC.prod f.hasCompactSupport).image
      ((continuous_fst.mul continuous_snd).mul (hθ.comp continuous_fst).inv)
  have ht := Γ.tendsto_coe_cofinite_of_isDiscrete
    (SetLike.isDiscrete_iff_discreteTopology.mpr ‹_›)
  have hfin := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hfin
  refine hfin.subset ?_
  rintro γ ⟨y, hy, hf⟩
  simp only [mem_compl_iff, mem_preimage, not_not]
  exact ⟨(y, y⁻¹ * γ * θ y), ⟨hy, subset_tsupport _ hf⟩, by simp [mul_assoc]⟩

end Topology

section Analysis

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem leftQuotientMap_mul_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) (x : G) :
    leftQuotientMap H (g * x) = leftQuotientMap H x := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simpa [mul_assoc] using H.inv_mem hg

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem isTwistedConjugate_symm {Γ : Subgroup G} {θ : Θ} {x y : G}
    (h : IsTwistedConjugate Γ θ x y) : IsTwistedConjugate Γ θ y x := by
  obtain ⟨g, hg, he⟩ := h
  refine ⟨g⁻¹, Γ.inv_mem hg, ?_⟩
  rw [← he, map_inv]
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
private theorem isTwistedConjugate_trans {Γ : Subgroup G} {θ : Θ} {x y z : G}
    (h₁ : IsTwistedConjugate Γ θ x y) (h₂ : IsTwistedConjugate Γ θ y z) :
    IsTwistedConjugate Γ θ x z := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨k, hk, rfl⟩ := h₂
  refine ⟨g * k, Γ.mul_mem hg hk, ?_⟩
  rw [map_mul]
  group

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem isClosed_twistedCentralizer' (θ : Θ) (hθ : Continuous θ) (δ : G)
    [IsTopologicalGroup G] [T2Space G] :
    IsClosed (twistedCentralizer θ δ : Set G) :=
  isClosed_eq ((continuous_inv.mul continuous_const).mul hθ) continuous_const

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [FunLike Θ G G]
  [MonoidHomClass Θ G G] in
private theorem enorm_nnreal_smul (r : ℝ≥0) (z : ℂ) : ‖(r : ℝ) • z‖ₑ = (r : ℝ≥0∞) * ‖z‖ₑ := by
  rw [enorm_smul, Real.enorm_of_nonneg (NNReal.coe_nonneg r), ENNReal.ofReal_coe_nnreal]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G]
  [BorelSpace G] in
private theorem countable_of_discreteTopology (Γ : Subgroup G) [DiscreteTopology Γ] :
    Countable Γ := by
  have : SecondCountableTopology Γ :=
    TopologicalSpace.Subtype.secondCountableTopology (Γ : Set G)
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] in
private theorem count_isFiniteMeasureOnCompacts (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSingletonClass Γ] : IsFiniteMeasureOnCompacts (Measure.count : Measure Γ) :=
  ⟨fun _ hK => Measure.count_apply_lt_top.mpr hK.finite_of_discrete⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] in
private theorem count_isOpenPosMeasure (Γ : Subgroup G) :
    (Measure.count : Measure Γ).IsOpenPosMeasure :=
  ⟨fun _ _ hU => Measure.count_ne_zero hU⟩

/-- The sum over `Γ` of the weighted absolute integrals of the twisted terms is finite. Its integrand
`Φ x = ∑' γ, ‖f (x⁻¹ γ θ x)‖` is left `Γ`-invariant, vanishes off `Γ · C` and is bounded on `C`, so
`∫ Φ ρ dμG = ∫_{Γ \ G} Φ dν ≤ M ν(Γ \ Γ C) < ⊤`. -/
private theorem tsum_lintegral_twisted_ne_top (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : Θ) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ))
    {C : Set G} (hC : IsCompact C)
    (hsupp : ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y)
    {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction Γ Measure.count ρ) :
    ∑' γ : Γ, ∫⁻ x, ‖f (x⁻¹ * γ * θ x)‖ₑ * ρ x ∂μG ≠ ⊤ := by
  classical
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have : Countable Γ := countable_of_discreteTopology Γ
  have : IsFiniteMeasureOnCompacts (Measure.count : Measure Γ) :=
    count_isFiniteMeasureOnCompacts Γ
  have : ν.Regular := hν.regular
  obtain ⟨B, hB⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hS := finite_twistedSupport Γ θ hθ f hC
  set M : ℝ≥0∞ := ∑ _γ ∈ hS.toFinset, ENNReal.ofReal B with hM
  have hMt : M ≠ ⊤ := ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  have hcont : ∀ γ : G, Continuous fun x : G => x⁻¹ * γ * θ x := fun γ =>
    (continuous_inv.mul continuous_const).mul hθ
  let Φ : G → ℝ≥0∞ := fun x => ∑' γ : Γ, ‖f (x⁻¹ * γ * θ x)‖ₑ
  have hΦm : Measurable Φ :=
    Measurable.tsum fun γ : Γ => (f.continuous.comp (hcont (γ : G))).enorm.measurable
  have hΦ : ∀ g : Γ, ∀ x, Φ (g.val * x) = Φ x := fun g x =>
    tsum_twistedConj_left_mul Γ θ hθΓ (fun z => ‖f z‖ₑ) g x
  have hbd : ∀ x, Φ x ≤ (leftQuotientMap Γ '' C).indicator (fun _ => M) (leftQuotientMap Γ x) := by
    intro x
    by_cases hx : ∃ γ : Γ, f (x⁻¹ * γ * θ x) ≠ 0
    · obtain ⟨γ, hγ⟩ := hx
      obtain ⟨g, hg, y, hy, rfl⟩ := hsupp x γ γ.2 hγ
      rw [indicator_of_mem (show leftQuotientMap Γ (g * y) ∈ leftQuotientMap Γ '' C from
        ⟨y, hy, (leftQuotientMap_mul_of_mem Γ hg y).symm⟩)]
      rw [show Φ (g * y) = Φ y from hΦ ⟨g, hg⟩ y]
      change ∑' γ : Γ, ‖f (y⁻¹ * γ * θ y)‖ₑ ≤ M
      rw [tsum_eq_sum (s := hS.toFinset)]
      · refine Finset.sum_le_sum fun δ _ => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hB _)
      · intro δ hδ
        by_contra h0
        exact hδ (hS.mem_toFinset.2 ⟨y, hy, fun h => h0 (by simp [h])⟩)
    · push Not at hx
      simp [Φ, hx]
  have hΦdesc : ∀ q, descend Γ Φ hΦ q ≤
      (leftQuotientMap Γ '' C).indicator (fun _ => M) q := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact hbd x
  have hfinC : ν (leftQuotientMap Γ '' C) < ⊤ :=
    (hC.image continuous_quotient_mk').measure_lt_top
  have heq : ∑' γ : Γ, ∫⁻ x, ‖f (x⁻¹ * γ * θ x)‖ₑ * ρ x ∂μG = ∫⁻ x, Φ x * ρ x ∂μG := by
    have hmeas : ∀ γ : Γ, AEMeasurable (fun x => ‖f (x⁻¹ * γ * θ x)‖ₑ * ρ x) μG := fun γ =>
      ((f.continuous.comp (hcont (γ : G))).enorm.measurable.mul hρ.measurable).aemeasurable
    rw [← lintegral_tsum hmeas]
    exact lintegral_congr fun x => ENNReal.tsum_mul_right
  rw [heq, ← hν.lintegral_descend_eq hΓc hρ Φ hΦm hΦ]
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hΦdesc) ?_)
  exact lt_of_le_of_lt (lintegral_indicator_const_le _ _) (ENNReal.mul_lt_top hMt.lt_top hfinC)

/-- **One class.** For `δ ∈ Γ`, a normalizing function `ρ₀` for `Γ` and conjugators `d c` with
`(d c)⁻¹ δ θ (d c) = c` for the elements `c` of the class of `δ`, `ρ_δ x = ∑' c, ρ₀ ((d c)⁻¹ x)` is a
normalizing function for `Γ ⊓ C_δ`. Therefore the orbit function descended to
`(Γ ⊓ C_δ) \ G` is integrable and its integral is the sum over the class of the weighted twisted
terms `∫ ρ₀ (x) f (x⁻¹ c θ x) dμG`. -/
private theorem hasSum_twistedClass (μG : Measure G) [μG.IsHaarMeasure]
    (Γ : Subgroup G) [DiscreteTopology Γ] (θ : Θ) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ)
    (f : C_c(G, ℂ)) {δ : G} (hδ : δ ∈ Γ)
    [MeasurableSpace (LeftQuotient (Γ ⊓ twistedCentralizer θ δ))]
    [BorelSpace (LeftQuotient (Γ ⊓ twistedCentralizer θ δ))]
    (νδ : Measure (LeftQuotient (Γ ⊓ twistedCentralizer θ δ)))
    (hνδ : IsCompatible (Γ ⊓ twistedCentralizer θ δ) μG Measure.count νδ)
    (ρ₀ : G → ℝ≥0) (hρc : Continuous ρ₀)
    (hρ : IsNormalizingFunction Γ Measure.count (fun x => (ρ₀ x : ℝ≥0∞)))
    (hfin : ∑' γ : Γ, ∫⁻ x, ‖f (x⁻¹ * γ * θ x)‖ₑ * (ρ₀ x : ℝ≥0∞) ∂μG ≠ ⊤) :
    HasSum (fun c : {γ : Γ // IsTwistedConjugate Γ θ δ γ} =>
        ∫ x, (ρ₀ x : ℝ) • f (x⁻¹ * c.1 * θ x) ∂μG)
      (∫ q, descend (Γ ⊓ twistedCentralizer θ δ) (fun x => f (x⁻¹ * δ * θ x))
        (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q ∂νδ) ∧
    Integrable (descend (Γ ⊓ twistedCentralizer θ δ) (fun x => f (x⁻¹ * δ * θ x))
        (apply_twistedConj_left_mul_of_le inf_le_right ⇑f)) νδ := by
  classical
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have hHc : IsClosed ((Γ ⊓ twistedCentralizer θ δ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hΓc.inter (isClosed_twistedCentralizer' θ hθ δ)
  have : DiscreteTopology (Γ ⊓ twistedCentralizer θ δ : Subgroup G) :=
    SetLike.isDiscrete_iff_discreteTopology.mp
      ((SetLike.isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology Γ›).mono inf_le_left)
  have : Countable Γ := countable_of_discreteTopology Γ
  have : IsFiniteMeasureOnCompacts
      (Measure.count : Measure (Γ ⊓ twistedCentralizer θ δ : Subgroup G)) :=
    count_isFiniteMeasureOnCompacts _
  have hdex : ∀ c : {γ : Γ // IsTwistedConjugate Γ θ δ γ},
      ∃ g : Γ, ((g : G))⁻¹ * δ * θ (g : G) = c.1 := by
    intro c
    obtain ⟨g, hg, h⟩ := c.2
    exact ⟨⟨g, hg⟩, h⟩
  choose d hd using hdex
  have hconj : ∀ c : {γ : Γ // IsTwistedConjugate Γ θ δ γ}, ∀ y : G,
      ((d c : G) * y)⁻¹ * δ * θ ((d c : G) * y) = y⁻¹ * c.1 * θ y := by
    intro c y
    rw [← hd c, map_mul]
    group
  let ρ : G → ℝ≥0∞ := fun x => ρ₀ x
  have hρm : Measurable ρ := (ENNReal.continuous_coe.comp hρc).measurable
  let ρδ : G → ℝ≥0∞ := fun x =>
    ∑' c : {γ : Γ // IsTwistedConjugate Γ θ δ γ}, ρ ((d c : G)⁻¹ * x)
  have hρδm : Measurable ρδ := Measurable.tsum fun c => hρm.comp (measurable_const_mul _)
  have hsum1 := ((isNormalizingFunction_count_iff Γ ρ).1 hρ).2
  have hρδ : IsNormalizingFunction (Γ ⊓ twistedCentralizer θ δ) Measure.count ρδ := by
    rw [isNormalizingFunction_count_iff]
    refine ⟨hρδm, fun x => ?_⟩
    rw [← hsum1 x, ← (Equiv.ofBijective _ (bijective_classMap Γ θ hθΓ hδ d hd)).tsum_eq
      (fun γ : Γ => ρ (γ * x))]
    change ∑' η : (Γ ⊓ twistedCentralizer θ δ : Subgroup G),
      ∑' c : {γ : Γ // IsTwistedConjugate Γ θ δ γ}, ρ ((d c : G)⁻¹ * (η * x)) = _
    rw [← ENNReal.tsum_prod]
    refine tsum_congr fun p => ?_
    simp [mul_assoc]
  have hφc : Continuous fun x : G => f (x⁻¹ * δ * θ x) :=
    f.continuous.comp ((continuous_inv.mul continuous_const).mul hθ)
  have hb : ∀ c : {γ : Γ // IsTwistedConjugate Γ θ δ γ},
      ∫⁻ x, ‖f (x⁻¹ * δ * θ x)‖ₑ * ρ ((d c : G)⁻¹ * x) ∂μG =
        ∫⁻ y, ‖f (y⁻¹ * c.1 * θ y)‖ₑ * ρ y ∂μG := by
    intro c
    rw [← lintegral_mul_left_eq_self
      (fun x => ‖f (x⁻¹ * δ * θ x)‖ₑ * ρ ((d c : G)⁻¹ * x)) (d c : G)]
    refine lintegral_congr fun y => ?_
    simp only [inv_mul_cancel_left, hconj]
  have hbsum : ∑' c : {γ : Γ // IsTwistedConjugate Γ θ δ γ},
      ∫⁻ y, ‖f (y⁻¹ * c.1 * θ y)‖ₑ * ρ y ∂μG ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun γ : Γ => ∫⁻ y, ‖f (y⁻¹ * γ * θ y)‖ₑ * ρ y ∂μG))
  have hA : ∫⁻ x, ‖f (x⁻¹ * δ * θ x)‖ₑ * ρδ x ∂μG =
      ∑' c : {γ : Γ // IsTwistedConjugate Γ θ δ γ},
        ∫⁻ y, ‖f (y⁻¹ * c.1 * θ y)‖ₑ * ρ y ∂μG := by
    have hmeas : ∀ c : {γ : Γ // IsTwistedConjugate Γ θ δ γ},
        AEMeasurable (fun x => ‖f (x⁻¹ * δ * θ x)‖ₑ * ρ ((d c : G)⁻¹ * x)) μG := fun c =>
      (hφc.enorm.measurable.mul (hρm.comp (measurable_const_mul _))).aemeasurable
    simp_rw [← hb]
    rw [← lintegral_tsum hmeas]
    exact lintegral_congr fun x => ENNReal.tsum_mul_left.symm
  have hφm : Measurable fun x : G => f (x⁻¹ * δ * θ x) := hφc.measurable
  have hdesc_int : Integrable (descend (Γ ⊓ twistedCentralizer θ δ)
      (fun x => f (x⁻¹ * δ * θ x)) (apply_twistedConj_left_mul_of_le inf_le_right ⇑f)) νδ := by
    refine ⟨(measurable_descend hHc _ hφm _).aestronglyMeasurable, ?_⟩
    have h := hνδ.lintegral_descend_eq hHc hρδ (fun x => ‖f (x⁻¹ * δ * θ x)‖ₑ)
      hφc.enorm.measurable (apply_twistedConj_left_mul_of_le inf_le_right (fun z => ‖f z‖ₑ))
    have heq : ∫⁻ q, ‖descend (Γ ⊓ twistedCentralizer θ δ) (fun x => f (x⁻¹ * δ * θ x))
        (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q‖ₑ ∂νδ =
        ∫⁻ q, descend (Γ ⊓ twistedCentralizer θ δ) (fun x => ‖f (x⁻¹ * δ * θ x)‖ₑ)
          (apply_twistedConj_left_mul_of_le inf_le_right (fun z => ‖f z‖ₑ)) q ∂νδ :=
      lintegral_congr fun q => Quotient.inductionOn q fun x => rfl
    unfold HasFiniteIntegral
    rw [heq, h, hA]
    exact hbsum.lt_top
  have hCq := hνδ.integral_descend_eq hHc hρδ (fun x => f (x⁻¹ * δ * θ x)) hφm
    (apply_twistedConj_left_mul_of_le inf_le_right ⇑f)
  have hρδfin : ∀ x, ρδ x ≠ ⊤ := by
    intro x
    have h1 : ρδ x ≤ ∑' η : (Γ ⊓ twistedCentralizer θ δ : Subgroup G), ρδ (η.val * x) := by
      simpa using ENNReal.le_tsum (f := fun η : (Γ ⊓ twistedCentralizer θ δ : Subgroup G) =>
        ρδ (η.val * x)) 1
    rw [((isNormalizingFunction_count_iff _ ρδ).1 hρδ).2 x] at h1
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h1
  let w : {γ : Γ // IsTwistedConjugate Γ θ δ γ} → G → ℂ := fun c x =>
    (ρ₀ ((d c : G)⁻¹ * x) : ℝ) • f (x⁻¹ * δ * θ x)
  have hD : ∀ x, (ρδ x).toReal • f (x⁻¹ * δ * θ x) = ∑' c, w c x := by
    intro x
    have hs : Summable fun c : {γ : Γ // IsTwistedConjugate Γ θ δ γ} =>
        (ρ ((d c : G)⁻¹ * x)).toReal :=
      ENNReal.summable_toReal (hρδfin x)
    change (∑' c, ρ ((d c : G)⁻¹ * x)).toReal • _ = _
    rw [ENNReal.tsum_toReal_eq (fun c => ENNReal.coe_ne_top), ← hs.tsum_smul_const]
    rfl
  have hwc : ∀ c, Continuous (w c) := fun c =>
    (NNReal.continuous_coe.comp (hρc.comp (continuous_const.mul continuous_id))).smul hφc
  have hwnorm : ∀ c, ∫⁻ x, ‖w c x‖ₑ ∂μG = ∫⁻ y, ‖f (y⁻¹ * c.1 * θ y)‖ₑ * ρ y ∂μG := by
    intro c
    rw [← hb c]
    refine lintegral_congr fun x => ?_
    rw [enorm_nnreal_smul, mul_comm]
  have hwint : ∀ c, Integrable (w c) μG := fun c =>
    ⟨(hwc c).aestronglyMeasurable, by
      unfold HasFiniteIntegral
      rw [hwnorm c]
      exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun c : {γ : Γ // IsTwistedConjugate Γ θ δ γ} =>
        ∫⁻ y, ‖f (y⁻¹ * c.1 * θ y)‖ₑ * ρ y ∂μG) c) hbsum.lt_top⟩
  have hwsum : Summable fun c => ∫ x, ‖w c x‖ ∂μG := by
    refine (ENNReal.summable_toReal hbsum).congr fun c => ?_
    rw [integral_norm_eq_lintegral_enorm (hwc c).aestronglyMeasurable, hwnorm c]
  have hE := hasSum_integral_of_summable_integral_norm hwint hwsum
  have hF : ∀ c : {γ : Γ // IsTwistedConjugate Γ θ δ γ},
      ∫ x, w c x ∂μG = ∫ x, (ρ₀ x : ℝ) • f (x⁻¹ * c.1 * θ x) ∂μG := by
    intro c
    rw [← integral_mul_left_eq_self (w c) (d c : G)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [w, inv_mul_cancel_left, hconj]
  refine ⟨?_, hdesc_int⟩
  have hlim : ∫ q, descend (Γ ⊓ twistedCentralizer θ δ) (fun x => f (x⁻¹ * δ * θ x))
      (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q ∂νδ = ∫ x, ∑' c, w c x ∂μG := by
    rw [hCq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hD x)
  rw [hlim]
  convert hE using 1
  funext c
  exact (hF c).symm

/-- **The unfolding of the twisted geometric side.** Let `G` be a Hausdorff, locally compact,
second countable group with a left Haar measure `μG`, `Γ` a discrete subgroup with
`IsCompatible Γ μG Measure.count ν`, `θ` continuous with `θ Γ ⊆ Γ`, and `f ∈ C_c(G, ℂ)` such that
every `x` with `f (x⁻¹ γ θ x) ≠ 0` for some `γ ∈ Γ` lies in `Γ · C` for a fixed compact `C`. Let
`r i ∈ Γ` be pairwise not `Γ`-`θ`-conjugate and meet every class of `γ ∈ Γ` on which
`x ↦ f (x⁻¹ γ θ x)` does not vanish, and let `νr i` be compatible with
`(μG, Measure.count)` on `(Γ ⊓ C_{r i}) \ G`. Then the descended orbit functions are integrable and

`∑ i, ∫ f (x⁻¹ r i θ x) dνr i = ∫_{Γ \ G} K(x, x) dν`

as an unconditionally convergent sum. -/
theorem twistedGeometricSide_unfolding (μG : Measure G) [μG.IsHaarMeasure]
    (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : Θ) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ))
    (hsupp : ∃ C : Set G, IsCompact C ∧
      ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y)
    {ι : Type*} (r : ι → Γ)
    (hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j)
    (hcover : ∀ γ : Γ, (∃ x : G, f (x⁻¹ * (γ : G) * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) (γ : G))
    [∀ i, MeasurableSpace (LeftQuotient (Γ ⊓ twistedCentralizer θ (r i : G)))]
    [∀ i, BorelSpace (LeftQuotient (Γ ⊓ twistedCentralizer θ (r i : G)))]
    (νr : ∀ i, Measure (LeftQuotient (Γ ⊓ twistedCentralizer θ (r i : G))))
    (hνr : ∀ i, IsCompatible (Γ ⊓ twistedCentralizer θ (r i : G)) μG Measure.count (νr i)) :
    HasSum (fun i => ∫ q, descend (Γ ⊓ twistedCentralizer θ (r i : G))
          (fun x => f (x⁻¹ * (r i : G) * θ x))
          (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q ∂νr i)
        (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν) ∧
      ∀ i, Integrable (descend (Γ ⊓ twistedCentralizer θ (r i : G))
          (fun x => f (x⁻¹ * (r i : G) * θ x))
          (apply_twistedConj_left_mul_of_le inf_le_right ⇑f)) (νr i) := by
  classical
  obtain ⟨C, hC, hsupp⟩ := hsupp
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  have : Countable Γ := countable_of_discreteTopology Γ
  have : IsFiniteMeasureOnCompacts (Measure.count : Measure Γ) :=
    count_isFiniteMeasureOnCompacts Γ
  have : (Measure.count : Measure Γ).IsOpenPosMeasure := count_isOpenPosMeasure Γ
  obtain ⟨ρ₀, hρc, hρ, -⟩ :=
    exists_continuous_isNormalizingFunction Γ hΓc (Measure.count : Measure Γ)
  have hfin := tsum_lintegral_twisted_ne_top μG Γ ν hν θ hθ hθΓ f hC hsupp hρ
  have hclass := fun i =>
    hasSum_twistedClass μG Γ θ hθ hθΓ f (r i).2 (νr i) (hνr i) ρ₀ hρc hρ hfin
  refine ⟨?_, fun i => (hclass i).2⟩
  have hcont : ∀ γ : G, Continuous fun x : G => f (x⁻¹ * γ * θ x) := fun γ =>
    f.continuous.comp ((continuous_inv.mul continuous_const).mul hθ)
  let F : Γ → G → ℂ := fun γ x => (ρ₀ x : ℝ) • f (x⁻¹ * γ * θ x)
  have hFc : ∀ γ : Γ, Continuous (F γ) := fun γ =>
    (NNReal.continuous_coe.comp hρc).smul (hcont γ)
  have hFnorm : ∀ γ : Γ, ∫⁻ x, ‖F γ x‖ₑ ∂μG =
      ∫⁻ x, ‖f (x⁻¹ * γ * θ x)‖ₑ * (ρ₀ x : ℝ≥0∞) ∂μG := fun γ =>
    lintegral_congr fun x => by rw [enorm_nnreal_smul, mul_comm]
  have hFint : ∀ γ : Γ, Integrable (F γ) μG := fun γ =>
    ⟨(hFc γ).aestronglyMeasurable, by
      unfold HasFiniteIntegral
      rw [hFnorm γ]
      exact lt_of_le_of_lt (ENNReal.le_tsum (f := fun γ : Γ =>
        ∫⁻ x, ‖f (x⁻¹ * γ * θ x)‖ₑ * (ρ₀ x : ℝ≥0∞) ∂μG) γ) hfin.lt_top⟩
  have hFsum : Summable fun γ : Γ => ∫ x, ‖F γ x‖ ∂μG := by
    refine (ENNReal.summable_toReal hfin).congr fun γ => ?_
    rw [integral_norm_eq_lintegral_enorm (hFc γ).aestronglyMeasurable, hFnorm γ]
  have h0 := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hKm : Measurable fun x : G => twistedKernel Γ θ f x x :=
    Measurable.tsum fun γ : Γ => (hcont (γ : G)).measurable
  have hdiag : ∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν = ∫ x, ∑' γ : Γ, F γ x ∂μG := by
    rw [twistedKernelDiagonal, hν.integral_descend_eq hΓc hρ _ hKm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [twistedKernel, ENNReal.coe_toReal, F]
    exact (tsum_const_smul'' _).symm
  rw [hdiag]
  let e : (Σ i : ι, {γ : Γ // IsTwistedConjugate Γ θ (r i : G) γ}) → Γ := fun p => p.2.1
  have he : Function.Injective e := by
    rintro ⟨i, ⟨γ, hc⟩⟩ ⟨j, ⟨γ', hc'⟩⟩ h
    change γ = γ' at h
    subst h
    obtain rfl : i = j := hr i j (isTwistedConjugate_trans hc (isTwistedConjugate_symm hc'))
    rfl
  have hz : ∀ γ ∉ Set.range e, ∫ x, F γ x ∂μG = 0 := by
    intro γ hγ
    have hzero : ∀ x, f (x⁻¹ * γ * θ x) = 0 := fun x => by
      by_contra hne
      obtain ⟨i, hi⟩ := hcover γ ⟨x, hne⟩
      exact hγ ⟨⟨i, γ, hi⟩, rfl⟩
    simp [F, hzero]
  exact ((he.hasSum_iff hz).2 h0).sigma fun i => (hclass i).1

/-- **The unfolding for a cocompact `Γ`**: if `Γ \ G` is compact, the conclusion of
`twistedGeometricSide_unfolding` holds for every `f ∈ C_c(G, ℂ)`, without a support hypothesis. -/
theorem twistedGeometricSide_unfolding_of_compactSpace (μG : Measure G) [μG.IsHaarMeasure]
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (LeftQuotient Γ)]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) (hν : IsCompatible Γ μG Measure.count ν)
    (θ : Θ) (hθ : Continuous θ) (hθΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : C_c(G, ℂ))
    {ι : Type*} (r : ι → Γ)
    (hr : ∀ i j, IsTwistedConjugate Γ θ (r i : G) (r j : G) → i = j)
    (hcover : ∀ γ : Γ, (∃ x : G, f (x⁻¹ * (γ : G) * θ x) ≠ 0) →
      ∃ i, IsTwistedConjugate Γ θ (r i : G) (γ : G))
    [∀ i, MeasurableSpace (LeftQuotient (Γ ⊓ twistedCentralizer θ (r i : G)))]
    [∀ i, BorelSpace (LeftQuotient (Γ ⊓ twistedCentralizer θ (r i : G)))]
    (νr : ∀ i, Measure (LeftQuotient (Γ ⊓ twistedCentralizer θ (r i : G))))
    (hνr : ∀ i, IsCompatible (Γ ⊓ twistedCentralizer θ (r i : G)) μG Measure.count (νr i)) :
    HasSum (fun i => ∫ q, descend (Γ ⊓ twistedCentralizer θ (r i : G))
          (fun x => f (x⁻¹ * (r i : G) * θ x))
          (apply_twistedConj_left_mul_of_le inf_le_right ⇑f) q ∂νr i)
        (∫ q, twistedKernelDiagonal Γ θ hθΓ f q ∂ν) ∧
      ∀ i, Integrable (descend (Γ ⊓ twistedCentralizer θ (r i : G))
          (fun x => f (x⁻¹ * (r i : G) * θ x))
          (apply_twistedConj_left_mul_of_le inf_le_right ⇑f)) (νr i) :=
  twistedGeometricSide_unfolding μG Γ ν hν θ hθ hθΓ f
    (exists_isCompact_twistedSupport_of_compactSpace Γ Subgroup.isClosed_of_discreteTopology θ f)
    r hr hcover νr hνr

end Analysis

end Langlands.TraceFormula
