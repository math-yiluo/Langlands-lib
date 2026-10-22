import Langlands.Representation.RankinSelberg.UnimodularityStatement
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Right invariance of normalized upper-unipotent Haar measure

Finite denominator clearing places every element in a compact open subgroup.
Regular Haar uniqueness and cancellation of the subgroup mass give right invariance.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

universe uF

/-- One nonzero integral scalar clears any finite set of field elements. -/
theorem common_integer_denominator {F : Type uF} [Field F] [ValuativeRel F]
    (s : Finset F) :
    ∃ d : F, d ≠ 0 ∧ d ∈ (ValuativeRel.valuation F).integer ∧
      ∀ x ∈ s, d * x ∈ (ValuativeRel.valuation F).integer := by
  classical
  let O := (ValuativeRel.valuation F).integer
  have single (x : F) : ∃ d : F, d ≠ 0 ∧ d ∈ O ∧ d * x ∈ O := by
    by_cases hx : x ∈ O
    · exact ⟨1, one_ne_zero, O.one_mem, by simpa using hx⟩
    · have hx0 : x ≠ 0 := by
        intro h
        exact hx (h ▸ O.zero_mem)
      have hi : x⁻¹ ∈ O :=
        ((ValuativeRel.valuation F).val_le_one_or_val_inv_le_one x).resolve_left hx
      exact ⟨x⁻¹, inv_ne_zero hx0, hi, by simp [hx0]⟩
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, O.one_mem, by simp⟩
  | @insert x s hx ih =>
      obtain ⟨d, hd0, hd, hs⟩ := ih
      obtain ⟨e, he0, he, hex⟩ := single x
      refine ⟨d * e, mul_ne_zero hd0 he0, O.mul_mem hd he, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simpa only [mul_assoc] using O.mul_mem hd hex
      · simpa only [mul_assoc, mul_left_comm, mul_comm] using O.mul_mem he (hs y hy)

private def scalingDiagonal {F : Type uF} [Field F] (n : ℕ) (d : F) (hd : d ≠ 0) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) F where
  val := Matrix.diagonal (fun i => (d ^ i.val)⁻¹)
  inv := Matrix.diagonal (fun i => d ^ i.val)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]

private theorem scalingDiagonal_conj_entry {F : Type uF} [Field F]
    (n : ℕ) (d : F) (hd : d ≠ 0)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (i j : Fin (n + 1)) :
    (scalingDiagonal n d hd * g * (scalingDiagonal n d hd)⁻¹) i j =
      (d ^ i.val)⁻¹ * g i j * d ^ j.val := by
  change (Matrix.diagonal (fun i : Fin (n + 1) => (d ^ i.val)⁻¹) * g.val *
    Matrix.diagonal (fun i : Fin (n + 1) => d ^ i.val)) i j = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem scalingDiagonal_conj_integral {F : Type uF} [Field F] [ValuativeRel F]
    (n : ℕ) (d : F) (hd : d ≠ 0) (hdi : d ∈ (ValuativeRel.valuation F).integer)
    (g : GeneralLinear.upperUnipotent (n + 1) F)
    (hg : ∀ i j, d * g.val i j ∈ (ValuativeRel.valuation F).integer) :
    ∀ i j, (scalingDiagonal n d hd * g.val * (scalingDiagonal n d hd)⁻¹) i j ∈
      (ValuativeRel.valuation F).integer := by
  intro i j
  rw [scalingDiagonal_conj_entry]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have he : j.val = i.val + (j.val - i.val - 1) + 1 := by
      have := Fin.lt_def.mp hij
      omega
    have heq : (d ^ i.val)⁻¹ * g.val i j * d ^ j.val =
        d ^ (j.val - i.val - 1) * (d * g.val i j) := by
      conv_lhs => rw [he, pow_add, pow_add, pow_one]
      field_simp
    rw [heq]
    exact ((ValuativeRel.valuation F).integer).mul_mem
      (((ValuativeRel.valuation F).integer).pow_mem hdi _) (hg i j)
  · simp [GeneralLinear.UpperUnipotent.entry_diag, hd]
  · simp [GeneralLinear.UpperUnipotent.entry_eq_zero g hji]

private theorem unipotent_localField_t2 (F : Type uF) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/-- Every upper-unipotent element is contained in a compact open subgroup. -/
theorem unipotent_exists_compact_open (F : Type uF) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℕ) (g : GeneralLinear.upperUnipotent (n + 1) F) :
    ∃ K : OpenSubgroup (GeneralLinear.upperUnipotent (n + 1) F),
      IsCompact (K : Set (GeneralLinear.upperUnipotent (n + 1) F)) ∧ g ∈ K := by
  classical
  have := unipotent_localField_t2 F
  let s := (Finset.univ.image (fun p : Fin (n + 1) × Fin (n + 1) => g.val p.1 p.2)) ∪
    (Finset.univ.image (fun p : Fin (n + 1) × Fin (n + 1) => (g⁻¹).val p.1 p.2))
  obtain ⟨d, hd, hdi, hs⟩ := common_integer_denominator s
  have hg (i j : Fin (n + 1)) : d * g.val i j ∈ (ValuativeRel.valuation F).integer := by
    apply hs
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hi (i j : Fin (n + 1)) : d * (g⁻¹).val i j ∈ (ValuativeRel.valuation F).integer := by
    apply hs
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  let D := scalingDiagonal n d hd
  let e := (Homeomorph.mulLeft D).trans (Homeomorph.mulRight D⁻¹)
  let f := (MulAut.conj D).toMonoidHom.comp (GeneralLinear.upperUnipotent (n + 1) F).subtype
  have hf : Continuous f := e.continuous.comp continuous_subtype_val
  let K := OpenSubgroup.comap f hf (Conductor.levelOpenSubgroup F n 0)
  refine ⟨K, ?_, ?_⟩
  · exact (e.isClosedEmbedding.comp
      (GeneralLinear.UpperUnipotent.isClosed (R := F) (n := n + 1)).isClosedEmbedding_subtypeVal).isCompact_preimage
        (Conductor.isCompact_levelOpenSubgroup F n 0)
  · change f g ∈ Conductor.levelSubgroup F n 0
    rw [Conductor.levelSubgroup_zero, Conductor.mem_integralSubgroup]
    constructor
    · exact scalingDiagonal_conj_integral n d hd hdi g hg
    · have he : (f g)⁻¹ = D * (g⁻¹).val * D⁻¹ := by simp [f, MulAut.conj_apply, mul_assoc]
      rw [he]
      exact scalingDiagonal_conj_integral n d hd hdi (g⁻¹) hi

private theorem map_right_eq_self_of_compact_open {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G) (hg : g ∈ K) :
    Measure.map (fun x => x * g) μ = μ := by
  have : (Measure.map (fun x => x * g) μ).Regular := Regular.map (Homeomorph.mulRight g)
  have hscale := isMulLeftInvariant_eq_smul_of_regular
    (Measure.map (fun x => x * g) μ) μ
  have hpre : (fun x : G => x * g) ⁻¹' (K : Set G) = K := by
    ext x
    exact K.toSubgroup.mul_mem_cancel_right hg
  have hm := congrArg (fun ν : Measure G => ν (K : Set G)) hscale
  rw [Measure.map_apply (measurable_mul_const g) K.isOpen.measurableSet, hpre,
    Measure.smul_apply] at hm
  have hzero : μ (K : Set G) ≠ 0 := K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
  have htop : μ (K : Set G) ≠ ⊤ := hK.measure_ne_top
  have he : (haarScalarFactor (Measure.map (fun x => x * g) μ) μ : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hzero htop).mp hm.symm
  rw [ENNReal.coe_eq_one.mp he, one_smul] at hscale
  exact hscale

/-- Intrinsic right invariance of the existing integral-normalized unipotent Haar measure. -/
theorem unipotentHaar_rightInvariant (F : Type uF) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)] :
    UnipotentHaarRightInvariantStatement F n := by
  have := unipotent_localField_t2 F
  have : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → F))
  have : LocallyCompactSpace (GeneralLinear.upperUnipotent (n + 1) F) :=
    GeneralLinear.UpperUnipotent.locallyCompactSpace
  refine ⟨fun g => ?_⟩
  obtain ⟨K, hK, hg⟩ := unipotent_exists_compact_open F n g
  exact map_right_eq_self_of_compact_open (unipotentHaar F n) K hK g hg

/-- The right-invariance instance for downstream quotient-measure constructions. -/
instance unipotentHaar_isMulRightInvariant (F : Type uF) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
    [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)] :
    IsMulRightInvariant (unipotentHaar F n) := unipotentHaar_rightInvariant F n

end Langlands.RankinSelberg
