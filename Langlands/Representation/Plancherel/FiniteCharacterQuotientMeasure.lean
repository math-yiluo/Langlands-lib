import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Separation.Hausdorff

/-! # Locally preserved measure on a finite character quotient -/

noncomputable section

open Function Set Topology MeasureTheory MeasureTheory.Measure
open scoped ENNReal Pointwise

namespace Langlands.Plancherel

/-- Every point has an open injectivity chart on which measurable subsets and
 their images have equal measures. -/
def IsLocallyMeasurePreserving {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y)
    (lambda : Measure X) (mu : Measure Y) : Prop :=
  ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U ∧
    ∀ E : Set X, MeasurableSet E → E ⊆ U →
      MeasurableSet (f '' E) ∧ mu (f '' E) = lambda E

variable {C : Type*} [CommGroup C] (S : Subgroup C)

private theorem quotient_preimage_image_eq_iUnion (E : Set C) :
    (QuotientGroup.mk : C → C ⧸ S) ⁻¹' (QuotientGroup.mk '' E) =
      ⋃ h : S, (h : C) • E := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hm : x / y ∈ S := QuotientGroup.eq_iff_div_mem.mp hxy.symm
    exact mem_iUnion.mpr ⟨⟨x / y, hm⟩, ⟨y, hy, div_mul_cancel x y⟩⟩
  · intro hx
    obtain ⟨h, y, hy, rfl⟩ := mem_iUnion.mp hx
    refine ⟨y, hy, ?_⟩
    change (QuotientGroup.mk y : C ⧸ S) = QuotientGroup.mk ((h : C) * y)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (h : C)).mpr h.property,
      one_mul]

private theorem quotient_translates_pairwise_disjoint {E : Set C}
    (hE : InjOn (QuotientGroup.mk : C → C ⧸ S) E) :
    Pairwise (Disjoint on fun h : S => (h : C) • E) := by
  intro h k hne
  apply disjoint_left.mpr
  rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
  have heq : (QuotientGroup.mk a : C ⧸ S) = QuotientGroup.mk b := by
    have hx := congrArg (QuotientGroup.mk : C → C ⧸ S) (hax.trans hbx.symm)
    simpa only [smul_eq_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff (h : C)).mpr h.property,
      (QuotientGroup.eq_one_iff (k : C)).mpr k.property, one_mul] using hx
  have hab := hE ha hb heq
  apply hne
  apply Subtype.ext
  exact mul_right_cancel (show (h : C) * a = (k : C) * a by
    simpa only [smul_eq_mul, hab] using hax.trans hbx.symm)

variable [TopologicalSpace C] [IsTopologicalGroup C]
variable [MeasurableSpace C] [BorelSpace C]
variable [MeasurableSpace (C ⧸ S)] [BorelSpace (C ⧸ S)]

/-- The quotient measure with counting measure on the finite fibers. It retains
 the scale of the supplied measure, rather than imposing total mass one. -/
def finiteCharacterQuotientMeasure [Finite S] (lambda : Measure C) : Measure (C ⧸ S) :=
  (Nat.card S : ℝ≥0∞)⁻¹ • Measure.map (QuotientGroup.mk : C → C ⧸ S) lambda

variable [Finite S]

omit [IsTopologicalGroup C] in
@[simp]
theorem finiteCharacterQuotientMeasure_apply (lambda : Measure C)
    {E : Set (C ⧸ S)} (hE : MeasurableSet E) :
    finiteCharacterQuotientMeasure S lambda E =
      (Nat.card S : ℝ≥0∞)⁻¹ * lambda (QuotientGroup.mk ⁻¹' E) := by
  rw [finiteCharacterQuotientMeasure, Measure.smul_apply,
    Measure.map_apply QuotientGroup.continuous_mk.measurable hE]
  rfl

omit [IsTopologicalGroup C] in
@[simp]
theorem finiteCharacterQuotientMeasure_univ (lambda : Measure C) :
    finiteCharacterQuotientMeasure S lambda univ =
      (Nat.card S : ℝ≥0∞)⁻¹ * lambda univ := by
  simp

omit [IsTopologicalGroup C] in
/-- Rescaling the original character measure rescales the quotient by the
 same amount. -/
theorem finiteCharacterQuotientMeasure_smul (lambda : Measure C) (c : ℝ≥0∞) :
    finiteCharacterQuotientMeasure S (c • lambda) =
      c • finiteCharacterQuotientMeasure S lambda := by
  simp only [finiteCharacterQuotientMeasure,
    Measure.map_smul c QuotientGroup.continuous_mk.measurable.aemeasurable, smul_smul]
  rw [mul_comm]

/-- An injective measurable piece has one disjoint translate per stabilizer
 element in its full inverse image. -/
theorem finiteCharacterQuotientMeasure_image (lambda : Measure C)
    [IsMulLeftInvariant lambda] {E : Set C} (hE : MeasurableSet E)
    (hinj : InjOn (QuotientGroup.mk : C → C ⧸ S) E)
    (himage : MeasurableSet ((QuotientGroup.mk : C → C ⧸ S) '' E)) :
    finiteCharacterQuotientMeasure S lambda (QuotientGroup.mk '' E) = lambda E := by
  classical
  let : Fintype S := Fintype.ofFinite S
  have hcard : (Nat.card S : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [finiteCharacterQuotientMeasure_apply S lambda himage,
    quotient_preimage_image_eq_iUnion,
    measure_iUnion (quotient_translates_pairwise_disjoint S hinj)
      (fun h => hE.const_smul (h : C))]
  simp only [measure_smul, tsum_fintype, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hcard (by simp), one_mul]

omit [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace (C ⧸ S)] [BorelSpace (C ⧸ S)] in
/-- A finite subgroup of a Hausdorff character group is discrete, so its
 quotient projection has open injectivity charts. -/
theorem isLocalHomeomorph_finiteCharacterQuotient [T2Space C] :
    IsLocalHomeomorph (QuotientGroup.mk : C → C ⧸ S) :=
  (S.isQuotientCoveringMap (Set.toFinite (S : Set C)).isDiscrete).isCoveringMap.isLocalHomeomorph

/-- The reciprocal-cardinality pushforward locally preserves the supplied
 invariant character measure. No probability normalization is assumed. -/
theorem isLocallyMeasurePreserving_finiteCharacterQuotient [T2Space C]
    (lambda : Measure C) [IsMulLeftInvariant lambda] :
    IsLocallyMeasurePreserving (QuotientGroup.mk : C → C ⧸ S) lambda
      (finiteCharacterQuotientMeasure S lambda) := by
  intro x
  obtain ⟨e, hx, he⟩ := isLocalHomeomorph_finiteCharacterQuotient S x
  refine ⟨e.source, e.open_source, hx, ?_, ?_⟩
  · rw [he]
    exact e.injOn
  · intro E hE hsub
    have himage : MeasurableSet ((QuotientGroup.mk : C → C ⧸ S) '' E) := by
      have hm := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
        (hE.preimage measurable_subtype_coe)
      convert hm using 1
      rw [he]
      ext y
      simp only [mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hsub hz⟩, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.val, hz, rfl⟩
    refine ⟨himage, finiteCharacterQuotientMeasure_image S lambda hE ?_ himage⟩
    rw [he]
    exact e.injOn.mono hsub

end Langlands.Plancherel
