import Langlands.HarmonicAnalysis.Distribution.Basic
import Langlands.LocalField.Canonical
import Langlands.Representation.Whittaker.GeneralLinear
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Character-weighted integration of product test functions

For a test function `α` on `G × (Y × G)`, the function
`y ↦ ∫ z, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)`
is a test function on `Y`. This gives a complex linear map
`SchwartzBruhat.characterAverage` and its algebraic dual
`Distribution.characterAverageDual`. See the paired Markdown for the
compact-tube argument, the hypotheses and the source correspondence.
-/

noncomputable section

open MeasureTheory Filter Topology Function

namespace Langlands.HarmonicAnalysis

universe uG uY uX uZ uF

namespace SchwartzBruhat

section ProductMeasurability

variable {X : Type uX} {Z : Type uZ} [TopologicalSpace X] [TopologicalSpace Z]
  [MeasurableSpace X] [MeasurableSpace Z] [OpensMeasurableSpace X] [OpensMeasurableSpace Z]

/-- A compact open subset of a product is a finite union of open rectangles, so it is
measurable for the product σ-algebra without any countability assumption. -/
theorem measurableSet_prod_of_isCompact_of_isOpen {W : Set (X × Z)} (hc : IsCompact W)
    (ho : IsOpen W) : MeasurableSet W := by
  have hrect : ∀ q ∈ W, ∃ U : Set X, ∃ V : Set Z,
      IsOpen U ∧ IsOpen V ∧ q.1 ∈ U ∧ q.2 ∈ V ∧ U ×ˢ V ⊆ W := fun q hq =>
    isOpen_prod_iff.mp ho q.1 q.2 hq
  choose U V hU hV hqU hqV hUV using hrect
  obtain ⟨t, ht⟩ := hc.elim_nhds_subcover' (fun q hq => U q hq ×ˢ V q hq)
    (fun q hq => ((hU q hq).prod (hV q hq)).mem_nhds ⟨hqU q hq, hqV q hq⟩)
  have hW : W = ⋃ q ∈ t, U q.1 q.2 ×ˢ V q.1 q.2 :=
    subset_antisymm ht (Set.iUnion₂_subset fun q _ => hUV q.1 q.2)
  rw [hW]
  exact Finset.measurableSet_biUnion t fun q _ =>
    (hU q.1 q.2).measurableSet.prod (hV q.1 q.2).measurableSet

/-- Every test function on a product is measurable for the product σ-algebra. -/
theorem measurable_prod (f : SchwartzBruhat (X × Z)) : Measurable (f : X × Z → ℂ) := by
  have key : ∀ S : Set ℂ, (0 : ℂ) ∉ S → MeasurableSet ((f : X × Z → ℂ) ⁻¹' S) := by
    intro S hS
    refine measurableSet_prod_of_isCompact_of_isOpen ?_ (f.locallyConstant S)
    refine (Hecke.TestFunction.isCompact_support f).of_isClosed_subset ?_ ?_
    · exact isOpen_compl_iff.mp (by simpa only [Set.preimage_compl] using f.locallyConstant Sᶜ)
    · intro q hq
      refine Function.mem_support.mpr fun h0 => hS ?_
      rwa [Set.mem_preimage, h0] at hq
  intro S _
  by_cases h0 : (0 : ℂ) ∈ S
  · have h := (key Sᶜ fun h => h h0).compl
    rwa [← Set.preimage_compl, compl_compl] at h
  · exact key S h0

/-- A test function on a product times a continuous measurable weight is integrable for
every measure finite on compact sets. -/
theorem integrable_mul_prod (f : SchwartzBruhat (X × Z)) {w : X × Z → ℂ}
    (hw : Continuous w) (hwm : Measurable w) (ρ : Measure (X × Z))
    [IsFiniteMeasureOnCompacts ρ] :
    Integrable (fun q => f q * w q) ρ := by
  have hK := Hecke.TestFunction.isCompact_support f
  have hKm : MeasurableSet (support (f : X × Z → ℂ)) :=
    measurableSet_prod_of_isCompact_of_isOpen hK (Hecke.TestFunction.isClopen_support f).isOpen
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f.continuous.mul hw).continuousOn
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero
    (s := support (f : X × Z → ℂ)) ?_ fun q hq => ?_
  · exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      ((measurable_prod f).mul hwm).aestronglyMeasurable
      ((ae_restrict_iff' hKm).mpr (Eventually.of_forall hC))
  · rw [Function.notMem_support.mp hq, zero_mul]

end ProductMeasurability

section CharacterAverage

variable {G : Type uG} {Y : Type uY} [TopologicalSpace G] [TopologicalSpace Y]

/-- The `y`-slice `z ↦ α (z.1, (y, z.2))` of a test function on `G × (Y × G)`. -/
def slice (α : SchwartzBruhat (G × (Y × G))) (y : Y) : SchwartzBruhat (G × G) :=
  ⟨fun z => α (z.1, (y, z.2)),
    α.locallyConstant.comp_continuous (by fun_prop),
    HasCompactSupport.intro'
      (((Hecke.TestFunction.isCompact_support α).image
          (by fun_prop : Continuous fun q : G × (Y × G) => (q.1, q.2.2))).of_isClosed_subset
        ((Hecke.TestFunction.isClopen_support α).isClosed.preimage
          (by fun_prop : Continuous fun z : G × G => (z.1, (y, z.2))))
        (fun z hz => ⟨(z.1, (y, z.2)), hz, rfl⟩))
      ((Hecke.TestFunction.isClopen_support α).isClosed.preimage
          (by fun_prop : Continuous fun z : G × G => (z.1, (y, z.2))))
      (fun _ hz => Function.notMem_support.mp hz)⟩

@[simp]
theorem slice_apply (α : SchwartzBruhat (G × (Y × G))) (y : Y) (z : G × G) :
    slice α y z = α (z.1, (y, z.2)) := rfl

variable [Monoid G]

/-- The weight `z ↦ ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹` is continuous. -/
theorem continuous_inverseCharacterWeight (χ : ContinuousMonoidHom G ℂˣ) :
    Continuous fun z : G × G => ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ := by
  have hχ : Continuous fun g : G => (χ g : ℂ) := Units.continuous_val.comp χ.continuous
  exact ((hχ.comp continuous_fst).mul (hχ.comp continuous_snd)).inv₀
    fun z => mul_ne_zero (χ z.1).ne_zero (χ z.2).ne_zero

/-- The weight `z ↦ ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹` is measurable for the product
σ-algebra. -/
theorem measurable_inverseCharacterWeight [MeasurableSpace G] [OpensMeasurableSpace G]
    (χ : ContinuousMonoidHom G ℂˣ) :
    Measurable fun z : G × G => ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ := by
  have hχ : Measurable fun g : G => (χ g : ℂ) :=
    (Units.continuous_val.comp χ.continuous).measurable
  exact ((hχ.comp measurable_fst).mul (hχ.comp measurable_snd)).inv

variable [MeasurableSpace G] [OpensMeasurableSpace G]
variable (χ : ContinuousMonoidHom G ℂˣ) (μ : Measure G)

/-- Every displayed slice of the character-weighted integral is integrable. -/
theorem integrable_characterAverage_slice [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (α : SchwartzBruhat (G × (Y × G))) (y : Y) :
    Integrable (fun z : G × G => α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹)
      (μ.prod μ) :=
  integrable_mul_prod (slice α y) (continuous_inverseCharacterWeight χ)
    (measurable_inverseCharacterWeight χ) (μ.prod μ)

/-- The raw character-weighted integral, before it is packaged as a test function. -/
def characterAverageIntegral (α : SchwartzBruhat (G × (Y × G))) (y : Y) : ℂ :=
  ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)

omit [OpensMeasurableSpace G] in
/-- A compact-tube argument proves local constancy of the character-weighted integral. -/
theorem characterAverageIntegral_isLocallyConstant (α : SchwartzBruhat (G × (Y × G))) :
    IsLocallyConstant (characterAverageIntegral χ μ α) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro y
  have hK : IsCompact ((fun q : G × (Y × G) => (q.1, q.2.2)) '' support (α : _ → ℂ)) :=
    (Hecke.TestFunction.isCompact_support α).image (by fun_prop)
  have he : ∀ᶠ y' in 𝓝 y,
      ∀ z ∈ (fun q : G × (Y × G) => (q.1, q.2.2)) '' support (α : _ → ℂ),
        α (z.1, (y', z.2)) = α (z.1, (y, z.2)) := by
    apply hK.eventually_forall_of_forall_eventually
    intro z _
    have h₁ : IsLocallyConstant fun q : Y × (G × G) => α (q.2.1, (q.1, q.2.2)) :=
      α.locallyConstant.comp_continuous (by fun_prop)
    have h₂ : IsLocallyConstant fun q : Y × (G × G) => α (q.2.1, (y, q.2.2)) :=
      α.locallyConstant.comp_continuous (by fun_prop)
    filter_upwards [h₁.eventually_eq (y, z), h₂.eventually_eq (y, z)] with q hq hq'
    exact hq.trans hq'.symm
  filter_upwards [he] with y' hy'
  have hpt : ∀ z : G × G, α (z.1, (y', z.2)) = α (z.1, (y, z.2)) := by
    intro z
    by_cases hz : z ∈ (fun q : G × (Y × G) => (q.1, q.2.2)) '' support (α : _ → ℂ)
    · exact hy' z hz
    · have h₁ : α (z.1, (y', z.2)) = 0 := by
        by_contra h
        exact hz ⟨(z.1, (y', z.2)), h, rfl⟩
      have h₂ : α (z.1, (y, z.2)) = 0 := by
        by_contra h
        exact hz ⟨(z.1, (y, z.2)), h, rfl⟩
      rw [h₁, h₂]
  simp only [characterAverageIntegral, hpt]

omit [OpensMeasurableSpace G] in
/-- The support of the character-weighted integral lies in the middle-coordinate projection
of the support of `α`. -/
theorem support_characterAverageIntegral_subset (α : SchwartzBruhat (G × (Y × G))) :
    support (characterAverageIntegral χ μ α) ⊆
      (fun q : G × (Y × G) => q.2.1) '' support (α : _ → ℂ) := by
  intro y hy
  by_contra h
  apply hy
  apply integral_eq_zero_of_ae
  refine Eventually.of_forall fun z => ?_
  have hz : α (z.1, (y, z.2)) = 0 := by
    by_contra h'
    exact h ⟨(z.1, (y, z.2)), h', rfl⟩
  simp [hz]

omit [OpensMeasurableSpace G] in
/-- The character-weighted integral has compact support. -/
theorem hasCompactSupport_characterAverageIntegral (α : SchwartzBruhat (G × (Y × G))) :
    HasCompactSupport (characterAverageIntegral χ μ α) := by
  have hcl : IsClosed (support (characterAverageIntegral χ μ α)) :=
    ((characterAverageIntegral_isLocallyConstant χ μ α).isClopen_fiber 0).compl.isClosed
  exact HasCompactSupport.intro'
    (((Hecke.TestFunction.isCompact_support α).image
      (by fun_prop : Continuous fun q : G × (Y × G) => q.2.1)).of_isClosed_subset hcl
      (support_characterAverageIntegral_subset χ μ α))
    hcl (fun _ hy => Function.notMem_support.mp hy)

variable [SFinite μ] [IsFiniteMeasureOnCompacts μ]

/-- Character-weighted integration of product test functions:
`α ↦ (y ↦ ∫ z, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ))`. -/
def characterAverage : SchwartzBruhat (G × (Y × G)) →ₗ[ℂ] SchwartzBruhat Y where
  toFun α := ⟨characterAverageIntegral χ μ α,
    characterAverageIntegral_isLocallyConstant χ μ α,
    hasCompactSupport_characterAverageIntegral χ μ α⟩
  map_add' α β := by
    ext y
    change ∫ z : G × G, (α (z.1, (y, z.2)) + β (z.1, (y, z.2))) *
        ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ) =
      ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ) +
        ∫ z : G × G, β (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)
    rw [← integral_add (integrable_characterAverage_slice χ μ α y)
      (integrable_characterAverage_slice χ μ β y)]
    simp only [add_mul]
  map_smul' c α := by
    ext y
    change ∫ z : G × G, (c * α (z.1, (y, z.2))) *
        ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ) =
      c * ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)
    rw [← integral_const_mul]
    simp only [mul_assoc]

/-- The pointwise evaluation law. -/
@[simp]
theorem characterAverage_apply (α : SchwartzBruhat (G × (Y × G))) (y : Y) :
    characterAverage χ μ α y =
      ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ) := rfl

/-- The support of the average lies in the middle-coordinate projection of the
(compact, clopen) support of `α`. -/
theorem support_characterAverage_subset (α : SchwartzBruhat (G × (Y × G))) :
    support (characterAverage χ μ α : Y → ℂ) ⊆
      (fun q : G × (Y × G) => q.2.1) '' tsupport (α : _ → ℂ) := by
  rw [Hecke.TestFunction.tsupport_eq_support]
  exact support_characterAverageIntegral_subset χ μ α

/-- The same inclusion for the topological support of the average. -/
theorem tsupport_characterAverage_subset (α : SchwartzBruhat (G × (Y × G))) :
    tsupport (characterAverage χ μ α : Y → ℂ) ⊆
      (fun q : G × (Y × G) => q.2.1) '' tsupport (α : _ → ℂ) := by
  rw [Hecke.TestFunction.tsupport_eq_support]
  exact support_characterAverage_subset χ μ α

/-- The same average for test functions on the left-associated product `(G × Y) × G`,
by precomposition with the existing pullback along `(Homeomorph.prodAssoc G Y G).symm`. -/
def characterAverageLeftAssoc : SchwartzBruhat ((G × Y) × G) →ₗ[ℂ] SchwartzBruhat Y :=
  (characterAverage χ μ).comp
    (Hecke.TestFunction.pullback (Homeomorph.prodAssoc G Y G).symm).toLinearMap

@[simp]
theorem characterAverageLeftAssoc_apply (α : SchwartzBruhat ((G × Y) × G)) (y : Y) :
    characterAverageLeftAssoc χ μ α y =
      ∫ z : G × G, α ((z.1, y), z.2) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ) := rfl

end CharacterAverage

end SchwartzBruhat

namespace Distribution

variable {G : Type uG} {Y : Type uY} [Monoid G] [TopologicalSpace G] [TopologicalSpace Y]
  [MeasurableSpace G] [OpensMeasurableSpace G]
variable (χ : ContinuousMonoidHom G ℂˣ) (μ : Measure G) [SFinite μ] [IsFiniteMeasureOnCompacts μ]

/-- The algebraic dual of character-weighted averaging: `D ↦ D ∘ characterAverage χ μ`. -/
def characterAverageDual : Distribution Y →ₗ[ℂ] Distribution (G × (Y × G)) :=
  (SchwartzBruhat.characterAverage χ μ).dualMap

@[simp]
theorem characterAverageDual_apply (D : Distribution Y) (α : SchwartzBruhat (G × (Y × G))) :
    characterAverageDual χ μ D α = D (SchwartzBruhat.characterAverage χ μ α) := rfl

end Distribution

section UpperUnipotent

open Langlands.GeneralLinear Langlands.Whittaker

/-- The specialization to the actual upper-unipotent subgroup `N` of `GL_{n+1}(F)` with its
Borel structure, the diagonal parameter space `Fin (n + 1) → Fˣ`, and the published
continuous standard character `standardCharacterContinuous ψ n`. -/
def standardCharacterAverage {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    UnitaryAdditiveCharacter F.Carrier →
      ∀ (μ : Measure (upperUnipotent (n + 1) F.Carrier)) [SFinite μ] [IsFiniteMeasureOnCompacts μ],
      SchwartzBruhat (upperUnipotent (n + 1) F.Carrier ×
          ((Fin (n + 1) → F.Carrierˣ) × upperUnipotent (n + 1) F.Carrier)) →ₗ[ℂ]
        SchwartzBruhat (Fin (n + 1) → F.Carrierˣ) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  haveI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  fun ψ μ => SchwartzBruhat.characterAverage (standardCharacterContinuous ψ n) μ

/-- Evaluation of the upper-unipotent specialization, with the inverse of both values of
the actual standard character. -/
theorem standardCharacterAverage_apply {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : Measure (upperUnipotent (n + 1) F.Carrier))
      [SFinite μ] [IsFiniteMeasureOnCompacts μ]
      (α : SchwartzBruhat (upperUnipotent (n + 1) F.Carrier ×
          ((Fin (n + 1) → F.Carrierˣ) × upperUnipotent (n + 1) F.Carrier)))
      (t : Fin (n + 1) → F.Carrierˣ),
      standardCharacterAverage F n ψ μ α t =
        ∫ z : upperUnipotent (n + 1) F.Carrier × upperUnipotent (n + 1) F.Carrier,
          α (z.1, (t, z.2)) *
            ((standardCharacter ψ n z.1 : ℂ) * (standardCharacter ψ n z.2 : ℂ))⁻¹ ∂(μ.prod μ) := by
  intros
  rfl

end UpperUnipotent

end Langlands.HarmonicAnalysis
