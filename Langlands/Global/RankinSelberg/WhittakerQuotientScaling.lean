import Langlands.Global.RankinSelberg.UnipotentConjugationModulus
import Langlands.Global.RankinSelberg.UnfoldingSteps
import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Analysis.Local.QuotientInvariantComparison
import Langlands.Automorphic.OperatorDeterminantSliceHaar
import Langlands.Automorphic.GroupSchemeParabolicWeilMeasure

/-! # Left translation by a normalizing point on `N_m(𝔸) \ GL_m(𝔸)`

Let `a ∈ GL_m(𝔸)` normalize `N_m(𝔸)`. Then `N_m(𝔸) g ↦ N_m(𝔸) a g` is a homeomorphism of
`N_m(𝔸) \ GL_m(𝔸)`, and it multiplies `whittakerQuotientMeasure` by the Haar modulus of
conjugation by `a` on `N_m(𝔸)`. For `a = ι_v(ϖ^λ)` the factor is
`N(v) ^ (-∑_(i<j) (λ_i - λ_j))`. The paired Markdown records the argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.WhittakerQuotientScaling

open UnipotentConjugationModulus

local instance scalingSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance scalingSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section CompactLift

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H]

/-- **Compact lifts.** If `Γ \ H` is compact, some compact subset of `H` maps onto it. -/
theorem exists_isCompact_image_mk_eq_univ (Γ : Subgroup H)
    [CompactSpace (LeftCosetSpace Γ)] :
    ∃ K : Set H, IsCompact K ∧ LeftCosetSpace.mk Γ '' K = Set.univ := by
  classical
  choose U hU using fun x : H => exists_compact_mem_nhds x
  have hcover : (Set.univ : Set (LeftCosetSpace Γ)) ⊆
      ⋃ x, LeftCosetSpace.mk Γ '' interior (U x) := by
    intro q _
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hU x).2, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun x => (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, U x, t.isCompact_biUnion fun x _ => (hU x).1, ?_⟩
  refine Set.eq_univ_of_forall fun q => ?_
  have hq := ht (Set.mem_univ q)
  simp only [Set.mem_iUnion] at hq
  obtain ⟨x, hx, y, hy, rfl⟩ := hq
  exact ⟨y, Set.mem_biUnion hx (interior_subset hy), rfl⟩

end CompactLift

variable (F : Type u) [Field F] [NumberField F] (m : ℕ)

local instance unipotentLocallyCompact : LocallyCompactSpace (unipotentAdelic F m) :=
  (isClosed_upperUnipotent_adelicPoints F m).locallyCompactSpace

/-- **Compact reduction in `N_m(𝔸)`.** Some compact `C ⊆ N_m(𝔸)` satisfies
`N_m(𝔸) = N_m(F) C`. -/
theorem exists_isCompact_unipotent_reduction :
    ∃ C : Set (unipotentAdelic F m), IsCompact C ∧ ∀ n : unipotentAdelic F m,
      ∃ c ∈ C, (n : Points F m) * (c : Points F m)⁻¹ ∈ unipotentRationalImage F m := by
  have := Unfolding.compactSpace_unipotentRationalQuotient F m
  obtain ⟨C, hC, hCu⟩ := exists_isCompact_image_mk_eq_univ
    (AdelicSubgroupPoints.rationalSubgroup F (Scheme F m) (upperUnipotent F m))
  refine ⟨C, hC, fun n => ?_⟩
  have hn : LeftCosetSpace.mk _ n ∈ LeftCosetSpace.mk
      (AdelicSubgroupPoints.rationalSubgroup F (Scheme F m) (upperUnipotent F m)) '' C := by
    rw [hCu]
    trivial
  obtain ⟨c, hc, hcn⟩ := hn
  refine ⟨c, hc, ?_⟩
  rw [LeftCosetSpace.mk_eq_mk_iff] at hcn
  rw [Unfolding.mem_unipotentRationalImage_iff]
  exact ⟨⟨n * c⁻¹, hcn⟩, by simp⟩

theorem toWhittakerQuotient_mk (x : Points F m) :
    toWhittakerQuotient F m (LeftCosetSpace.mk _ x) =
      LeftCosetSpace.mk (unipotentAdelic F m) x :=
  rfl

/-- `whittakerQuotientMeasure` is locally finite. -/
theorem isLocallyFiniteMeasure_whittakerQuotientMeasure :
    IsLocallyFiniteMeasure (whittakerQuotientMeasure F m) := by
  have := LeftCosetSpace.isLocallyFiniteMeasure_haarQuotientMeasure
    (unipotentRationalImage F m) (isDiscrete_unipotentRationalImage F m)
  refine ⟨fun q => ?_⟩
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ q
  obtain ⟨V, hVc, hVx⟩ := exists_compact_mem_nhds x
  obtain ⟨C, hC, hred⟩ := exists_isCompact_unipotent_reduction F m
  let P : Set (Points F m) :=
    (fun p : unipotentAdelic F m × Points F m => (p.1 : Points F m) * p.2) '' (C ×ˢ V)
  have hP : IsCompact P :=
    (hC.prod hVc).image ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)
  have hOopen : IsOpen (LeftCosetSpace.mk (unipotentAdelic F m) '' interior V) :=
    (LeftCosetSpace.isOpenQuotientMap_mk _).isOpenMap _ isOpen_interior
  refine ⟨LeftCosetSpace.mk _ '' interior V,
    hOopen.mem_nhds ⟨x, mem_interior_iff_mem_nhds.2 hVx, rfl⟩, ?_⟩
  rw [whittakerQuotientMeasure, Measure.map_apply (measurable_toWhittakerQuotient F m)
    hOopen.measurableSet]
  have hsub : toWhittakerQuotient F m ⁻¹' (LeftCosetSpace.mk _ '' interior V) ⊆
      LeftCosetSpace.mk (unipotentRationalImage F m) '' P := by
    intro z hz
    obtain ⟨z, rfl⟩ := LeftCosetSpace.mk_surjective _ z
    obtain ⟨y, hyV, hyz⟩ := hz
    rw [toWhittakerQuotient_mk, LeftCosetSpace.mk_eq_mk_iff] at hyz
    obtain ⟨c, hcC, hc⟩ := hred ⟨z * y⁻¹, hyz⟩
    refine ⟨(c : Points F m) * y, ⟨(c, y), ⟨hcC, interior_subset hyV⟩, rfl⟩, ?_⟩
    rw [LeftCosetSpace.mk_eq_mk_iff]
    have he : z * ((c : Points F m) * y)⁻¹ = z * y⁻¹ * (c : Points F m)⁻¹ := by group
    rw [he]
    exact hc
  exact (measure_mono hsub).trans_lt
    (hP.image (LeftCosetSpace.continuous_mk _)).measure_lt_top

theorem toWhittakerQuotient_rightTranslate (g : Points F m)
    (z : LeftCosetSpace (unipotentRationalImage F m)) :
    toWhittakerQuotient F m (LeftCosetSpace.rightTranslate _ g z) =
      LeftCosetSpace.rightTranslate _ g (toWhittakerQuotient F m z) := by
  induction z using Quotient.inductionOn with
  | h x => rfl

/-- `whittakerQuotientMeasure` is invariant under right translation by `GL_m(𝔸)`. -/
theorem measurePreserving_rightTranslate (g : Points F m) :
    MeasurePreserving (LeftCosetSpace.rightTranslate (unipotentAdelic F m) g)
      (whittakerQuotientMeasure F m) (whittakerQuotientMeasure F m) := by
  have := Automorphic.OperatorDeterminantSlice.haar_isMulRightInvariant F m
  have h := LeftCosetSpace.measurePreserving_rightTranslate_haarQuotientMeasure
    (unipotentRationalImage F m) (isDiscrete_unipotentRationalImage F m) g
  have hm := (LeftCosetSpace.continuous_rightTranslate (unipotentAdelic F m) g).measurable
  refine ⟨hm, ?_⟩
  have hc : LeftCosetSpace.rightTranslate (unipotentAdelic F m) g ∘ toWhittakerQuotient F m =
      toWhittakerQuotient F m ∘ LeftCosetSpace.rightTranslate _ g :=
    funext fun z => (toWhittakerQuotient_rightTranslate F m g z).symm
  rw [whittakerQuotientMeasure, Measure.map_map hm (measurable_toWhittakerQuotient F m), hc,
    ← Measure.map_map (measurable_toWhittakerQuotient F m) h.measurable, h.map_eq]

theorem whittakerQuotientMeasure_ne_zero : whittakerQuotientMeasure F m ≠ 0 := by
  rw [whittakerQuotientMeasure, Ne,
    Measure.map_eq_zero_iff (measurable_toWhittakerQuotient F m).aemeasurable]
  exact LeftCosetSpace.haarQuotientMeasure_ne_zero _ _

/-- `whittakerQuotientMeasure` is regular. -/
theorem regular_whittakerQuotientMeasure : (whittakerQuotientMeasure F m).Regular := by
  have := isLocallyFiniteMeasure_whittakerQuotientMeasure F m
  exact Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

/-- `GL_m(𝔸)` is unimodular: conjugation has Haar modulus one. -/
theorem mulEquivHaarChar_conjugation (a : Points F m) :
    mulEquivHaarChar (conjugation a) = 1 := by
  have := Automorphic.OperatorDeterminantSlice.haar_isMulRightInvariant F m
  apply HarmonicAnalysis.mulEquivHaarChar_eq_of_smul_map (Measure.haar : Measure (Points F m))
  rw [one_smul]
  have h : (conjugation a : Points F m → Points F m) = (fun x => x * a⁻¹) ∘ fun x => a * x :=
    funext fun x => rfl
  rw [h, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
    map_mul_left_eq_self, map_mul_right_eq_self]

/-- Left translation `N_m(𝔸) g ↦ N_m(𝔸) a g` on `N_m(𝔸) \ GL_m(𝔸)`, through the chosen
representatives. -/
def leftShift (a : Points F m) : WhittakerQuotient F m → WhittakerQuotient F m :=
  fun q => LeftCosetSpace.mk (unipotentAdelic F m) (a * q.out)

variable {F m}

/-- For `a` normalizing `N_m(𝔸)`, the left translation as a homeomorphism: the quotient
automorphism of conjugation by `a`, followed by right translation by `a`. -/
def leftShiftHomeomorph (a : Points F m)
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m) :
    WhittakerQuotient F m ≃ₜ WhittakerQuotient F m :=
  (QuotientIntegration.quotientAutomorphism (unipotentAdelic F m) (conjugation a) hα).trans
    (LeftCosetSpace.rightTranslateHomeomorph (unipotentAdelic F m) a)

theorem coe_leftShiftHomeomorph (a : Points F m)
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m) :
    ⇑(leftShiftHomeomorph a hα) = leftShift F m a := by
  funext q
  conv_lhs => rw [← Quotient.out_eq q]
  change LeftCosetSpace.mk _ (a * q.out * a⁻¹ * a) = LeftCosetSpace.mk _ (a * q.out)
  rw [inv_mul_cancel_right]

theorem leftShift_mk (a : Points F m)
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m)
    (x : Points F m) :
    leftShift F m a (LeftCosetSpace.mk _ x) = LeftCosetSpace.mk _ (a * x) := by
  rw [← coe_leftShiftHomeomorph a hα]
  change LeftCosetSpace.mk _ (a * x * a⁻¹ * a) = LeftCosetSpace.mk _ (a * x)
  rw [inv_mul_cancel_right]

theorem leftShiftHomeomorph_symm_mk (a : Points F m)
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m)
    (x : Points F m) :
    (leftShiftHomeomorph a hα).symm (LeftCosetSpace.mk _ x) =
      LeftCosetSpace.mk _ (a⁻¹ * x) := by
  rw [Homeomorph.symm_apply_eq, coe_leftShiftHomeomorph, leftShift_mk a hα, mul_inv_cancel_left]

/-- **Scaling of the Whittaker quotient measure.** For `a` normalizing `N_m(𝔸)`, the left
translation by `a` multiplies `whittakerQuotientMeasure` by the Haar modulus of conjugation
by `a` on `N_m(𝔸)`. -/
theorem map_leftShift (a : Points F m)
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m) :
    Measure.map (leftShift F m a) (whittakerQuotientMeasure F m) =
      ((mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism (unipotentAdelic F m)
        (conjugation a) hα) : ℝ≥0) : ℝ≥0∞) • whittakerQuotientMeasure F m := by
  have hN : IsClosed (unipotentAdelic F m : Set (Points F m)) :=
    isClosed_upperUnipotent_adelicPoints F m
  have := Automorphic.OperatorDeterminantSlice.haar_isMulRightInvariant F m
  have := Unfolding.compactSpace_unipotentRationalQuotient F m
  have := AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F
    (Scheme F m) (upperUnipotent F m)
  have := regular_whittakerQuotientMeasure F m
  obtain ⟨ν₀, hν₀⟩ := QuotientIntegration.compatibleMeasureExists (unipotentAdelic F m) hN
    (Measure.haar : Measure (Points F m)) (Measure.haar : Measure (unipotentAdelic F m))
  have : ν₀.Regular := hν₀.regular
  obtain ⟨C, -, hCeq⟩ := QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient
    (unipotentAdelic F m) hN (Measure.haar : Measure (unipotentAdelic F m))
    (whittakerQuotientMeasure F m) ν₀ (whittakerQuotientMeasure_ne_zero F m) hν₀.nonzero
    (fun g => measurePreserving_rightTranslate F m g) hν₀.right_invariant
  have hαQ := hν₀.map_quotientAutomorphism (unipotentAdelic F m) hN (conjugation a) hα
  rw [mulEquivHaarChar_conjugation F m a, div_one] at hαQ
  have hrt := (measurePreserving_rightTranslate F m a).map_eq
  have hcomp : leftShift F m a = LeftCosetSpace.rightTranslate (unipotentAdelic F m) a ∘
      QuotientIntegration.quotientAutomorphism (unipotentAdelic F m) (conjugation a) hα := by
    rw [← coe_leftShiftHomeomorph a hα]
    rfl
  have hmR := (LeftCosetSpace.continuous_rightTranslate (unipotentAdelic F m) a).measurable
  have hmQ := (QuotientIntegration.quotientAutomorphism (unipotentAdelic F m) (conjugation a)
    hα).continuous.measurable
  rw [hcomp, ← Measure.map_map hmR hmQ]
  rw [hCeq] at hrt ⊢
  rw [Measure.map_smul _ hmR.aemeasurable] at hrt
  rw [Measure.map_smul _ hmQ.aemeasurable, hαQ, Measure.map_smul _ hmR.aemeasurable,
    Measure.map_smul _ hmR.aemeasurable, smul_comm (ENNReal.ofReal C), hrt]

/-- **The Whittaker quotient measure under `ι_v(ϖ^λ)`.** Left translation by
`ι_v(ϖ^λ)` multiplies `whittakerQuotientMeasure` by `N(v) ^ (-∑_(i<j) (λ_i - λ_j))`. -/
theorem map_leftShift_localPoint_torus (v : FinitePlace F) {ϖ : (FiniteCompletion F v)ˣ}
    (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement
      (WhittakerCellAdelicScaling.valuation F v) ϖ)
    (lam : Fin m → ℤ) :
    Measure.map (leftShift F m (localPoint F m v (GeneralLinear.Iwasawa.torus ϖ lam)))
        (whittakerQuotientMeasure F m) =
      (((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-modulusExponent lam) : ℝ≥0) : ℝ≥0∞) •
        whittakerQuotientMeasure F m := by
  rw [map_leftShift _ (conj_localPoint_torus_mem_iff F v ϖ lam),
    mulEquivHaarChar_conj_localPoint_torus F v hϖ lam]

/-- Integrability is preserved by a left translation that scales the measure. -/
theorem integrable_comp_leftShift (a : Points F m)
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m)
    {δ : ℝ≥0}
    (hδ : Measure.map (leftShift F m a) (whittakerQuotientMeasure F m) =
      (δ : ℝ≥0∞) • whittakerQuotientMeasure F m)
    {f : WhittakerQuotient F m → ℂ} (hf : Integrable f (whittakerQuotientMeasure F m)) :
    Integrable (fun q => f (leftShift F m a q)) (whittakerQuotientMeasure F m) := by
  let e := (leftShiftHomeomorph a hα).toMeasurableEquiv
  have he : ⇑e = leftShift F m a := coe_leftShiftHomeomorph a hα
  have h : Integrable f (Measure.map e (whittakerQuotientMeasure F m)) →
      Integrable (f ∘ e) (whittakerQuotientMeasure F m) := (integrable_map_equiv e f).mp
  rw [he, hδ] at h
  exact h (hf.smul_measure ENNReal.coe_ne_top)

/-- The change of variables for a set integral along a left translation that scales the
measure by `δ`. -/
theorem setIntegral_comp_leftShift (a : Points F m)
    (hα : ∀ x, conjugation a x ∈ unipotentAdelic F m ↔ x ∈ unipotentAdelic F m)
    {δ : ℝ≥0}
    (hδ : Measure.map (leftShift F m a) (whittakerQuotientMeasure F m) =
      (δ : ℝ≥0∞) • whittakerQuotientMeasure F m)
    (U : Set (WhittakerQuotient F m)) (f : WhittakerQuotient F m → ℂ) :
    ∫ q in U, f (leftShift F m a q) ∂whittakerQuotientMeasure F m =
      (δ : ℝ) • ∫ q in (leftShiftHomeomorph a hα).symm ⁻¹' U, f q
        ∂whittakerQuotientMeasure F m := by
  let e := (leftShiftHomeomorph a hα).toMeasurableEquiv
  have he : ⇑e = leftShift F m a := coe_leftShiftHomeomorph a hα
  have hpre : e ⁻¹' ((leftShiftHomeomorph a hα).symm ⁻¹' U) = U := by
    ext q
    simp [e]
  have h : ∫ y in (leftShiftHomeomorph a hα).symm ⁻¹' U, f y
        ∂Measure.map e (whittakerQuotientMeasure F m) =
      ∫ x in e ⁻¹' ((leftShiftHomeomorph a hα).symm ⁻¹' U), f (e x)
        ∂whittakerQuotientMeasure F m :=
    e.measurableEmbedding.setIntegral_map f _
  rw [hpre, he, hδ, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal] at h
  rw [← h]

end Langlands.Global.RankinSelbergGlobal.WhittakerQuotientScaling
