import Langlands.Representation.GodementJacquet.ComplexJacquetRectangleAffine
import Langlands.Group.GL.UpperUnipotentEntryCoordinates
import Langlands.HarmonicAnalysis.AdjacentRankUnipotentMatrix

/-! # Unipotent and last-column coordinates for Jacquet's rectangular arrays -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {r : ℕ}
private abbrev StrictEntryPair (s : ℕ) := {p : Fin s × Fin s // p.1 < p.2}
local notation "m" => r + 1
local notation "I" => Fin m
local notation "J" => StrictEntryPair m
local notation "U" => upperUnipotent m ℂ
local notation "Z" => I → ℂ
local notation "E" => J → ℂ
local notation "L" => jacquetRectangleLeftIndex m
local notation "D" => jacquetRectangleRightIndex m
local notation "R" => Matrix I (Fin (m + 1)) ℂ

local instance jacquetRectangleUnipotentMeasurable : MeasurableSpace U := borel _
local instance jacquetRectangleUnipotentBorel : BorelSpace U := ⟨rfl⟩

private def leftEntryMap : J ⊕ I → L
  | .inl p =>
      ⟨(p.val.1, p.val.2.castSucc.rev), by
        have h := p.property
        change p.val.1.val < p.val.2.val at h
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega⟩
  | .inr i => ⟨(i, 0), by simpa only [Fin.val_zero, add_zero] using i.isLt⟩

private theorem leftEntryMap_bijective : Function.Bijective (leftEntryMap (r := r)) := by
  constructor
  · intro s t h
    have h' := congrArg Subtype.val h
    rcases s with s | s <;> rcases t with t | t
    · congr 1
      apply Subtype.ext
      have hfst : s.val.1 = t.val.1 := congrArg (fun p : I × Fin (m + 1) => p.1) h'
      have he : s.val.2.castSucc.rev = t.val.2.castSucc.rev := congrArg Prod.snd h'
      exact Prod.ext hfst (Fin.castSucc_injective _ (Fin.rev_injective he))
    · have he : s.val.2.castSucc.rev = (0 : Fin (m + 1)) := congrArg Prod.snd h'
      have he' : s.val.2.castSucc = Fin.last m := by
        simpa only [Fin.rev_rev, Fin.rev_zero] using congrArg Fin.rev he
      exact (Fin.castSucc_ne_last _ he').elim
    · have he : (0 : Fin (m + 1)) = t.val.2.castSucc.rev := congrArg Prod.snd h'
      have he' : t.val.2.castSucc = Fin.last m := by
        simpa only [Fin.rev_rev, Fin.rev_zero] using congrArg Fin.rev he.symm
      exact (Fin.castSucc_ne_last _ he').elim
    · exact congrArg Sum.inr (congrArg Prod.fst h')
  · rintro ⟨⟨i, j⟩, h⟩
    by_cases hj : j = 0
    · subst j
      exact ⟨.inr i, rfl⟩
    · have hj₀ : 0 < j.val := by
        by_contra! h0
        exact hj (Fin.ext (Nat.eq_zero_of_le_zero h0))
      change i.val + j.val < m at h
      let k : I := ⟨m - j.val, by omega⟩
      have hik : i < k := by
        change i.val < m - j.val
        omega
      refine ⟨.inl ⟨(i, k), hik⟩, Subtype.ext (Prod.ext rfl ?_)⟩
      apply Fin.ext
      simp only [leftEntryMap, Fin.val_rev, Fin.val_castSucc, k]
      omega

private def rightEntryMap : J ⊕ I → D
  | .inl p =>
      ⟨(p.val.1.rev, p.val.2.castSucc), by
        have h := p.property
        change p.val.1.val < p.val.2.val at h
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega⟩
  | .inr i => ⟨(i.rev, Fin.last m), by
      change ¬i.rev.val + m < m
      omega⟩

private theorem rightEntryMap_bijective : Function.Bijective (rightEntryMap (r := r)) := by
  constructor
  · intro s t h
    have h' := congrArg Subtype.val h
    rcases s with s | s <;> rcases t with t | t
    · congr 1
      apply Subtype.ext
      have he : s.val.1.rev = t.val.1.rev := congrArg Prod.fst h'
      have he' : s.val.2.castSucc = t.val.2.castSucc := congrArg Prod.snd h'
      exact Prod.ext (Fin.rev_injective he) (Fin.castSucc_injective _ he')
    · have he : s.val.2.castSucc = Fin.last m := congrArg Prod.snd h'
      exact (Fin.castSucc_ne_last _ he).elim
    · have he : Fin.last m = t.val.2.castSucc := congrArg Prod.snd h'
      exact (Fin.castSucc_ne_last _ he.symm).elim
    · exact congrArg Sum.inr (Fin.rev_injective (congrArg Prod.fst h'))
  · rintro ⟨⟨i, j⟩, h⟩
    refine Fin.lastCases ?_ (fun j => ?_) j h
    · intro h
      exact ⟨.inr i.rev, Subtype.ext (Prod.ext (Fin.rev_rev i) rfl)⟩
    · intro h
      have he : i.rev < j := by
        change ¬i.val + j.val < m at h
        rw [Fin.lt_def, Fin.val_rev]
        omega
      exact ⟨.inl ⟨(i.rev, j), he⟩, Subtype.ext (Prod.ext (Fin.rev_rev i) rfl)⟩

private def leftEntryEquiv : J ⊕ I ≃ L :=
  Equiv.ofBijective leftEntryMap leftEntryMap_bijective

private def rightEntryEquiv : J ⊕ I ≃ D :=
  Equiv.ofBijective rightEntryMap rightEntryMap_bijective

private def rectangleReindex {α : Type*} (e : J ⊕ I ≃ α) : (E × Z) ≃L[ℝ] (α → ℂ) :=
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ J I (fun _ => ℂ)).symm.trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : α => ℂ) e)

private theorem rectangleReindex_apply {α : Type*} (e : J ⊕ I ≃ α) (p : E × Z) (s : J ⊕ I) :
    rectangleReindex e p (e s) = Sum.elim p.1 p.2 s := by
  unfold rectangleReindex
  rw [ContinuousLinearEquiv.trans_apply, complexCoordinateReindex_apply]
  change (ContinuousLinearEquiv.sumPiEquivProdPi ℝ J I (fun _ => ℂ)).symm p (e.symm (e s)) = _
  rw [e.symm_apply_apply]
  cases s <;> rfl

private theorem measurePreserving_rectangleReindex {α : Type*} [Fintype α] (a : ℂˣ)
    (e : J ⊕ I ≃ α) :
    MeasurePreserving (rectangleReindex e)
      ((complexCoordinateMeasure J a).prod (complexCoordinateMeasure I a))
      (complexCoordinateMeasure α a) := by
  let ν := (complexSelfDualMeasure a).measure
  let : ν.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  have h := measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ν)
  exact (measurePreserving_complexCoordinateReindex a e).comp
    (h.symm (MeasurableEquiv.sumPiEquivProdPi fun _ : J ⊕ I => ℂ))

private theorem matrix_mul_weylLong_apply (X : R) (i : I) (j : Fin (m + 1)) :
    (X * (weylLong (m + 1) ℂ).val) i j = X i j.rev := by
  classical
  change (∑ k, X i k * weylLong (m + 1) ℂ k j) = X i j.rev
  simp [weylLong_entry, mul_ite]

private theorem weylLong_mul_matrix_apply (X : R) (i : I) (j : Fin (m + 1)) :
    ((weylLong m ℂ).val * X) i j = X i.rev j := by
  classical
  change (∑ k, weylLong m ℂ i k * X k j) = X i.rev j
  simp only [weylLong_entry, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i.rev]
  · simp
  · intro k _ hk
    rw [ite_eq_right_iff]
    intro h
    exact (hk (Fin.rev_injective (h.trans (Fin.rev_rev i).symm))).elim
  · simp

private theorem leftArray_eq (p : E × Z) :
    jacquetRectangleLeftArray (rectangleReindex leftEntryEquiv p) =
      rectangularJoin ((upperEntryCoordinates m).symm p.1).val.val p.2 *
        (weylLong (m + 1) ℂ).val := by
  let u : U := (upperEntryCoordinates m).symm p.1
  let x := rectangleReindex leftEntryEquiv p
  ext i j
  rw [matrix_mul_weylLong_apply]
  suffices h : ∀ k : Fin (m + 1), jacquetRectangleLeftArray x i k.rev = rectangularJoin u.val.val p.2 i k by
    simpa only [Fin.rev_rev, x, u] using h j.rev
  intro k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · have hi : i.val + (0 : Fin (m + 1)).val < m := by
      simpa only [Fin.val_zero, add_zero] using i.isLt
    rw [Fin.rev_last, rectangularJoin_last, jacquetRectangleLeftArray_free x i 0 hi]
    exact rectangleReindex_apply leftEntryEquiv p (.inr i)
  · rw [rectangularJoin_castSucc]
    rcases lt_trichotomy i k with hk | rfl | hk
    · have h : i.val + k.castSucc.rev.val < m := by
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega
      rw [jacquetRectangleLeftArray_free x i _ h, upperEntryCoordinates_symm_upper p.1 hk]
      exact rectangleReindex_apply leftEntryEquiv p (.inl ⟨(i, k), hk⟩)
    · have h : i.val + i.castSucc.rev.val = m := by
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega
      rw [jacquetRectangleLeftArray_fixed x i _ (by omega), ite_eq_left h, u.property.2 i]
    · have h : m < i.val + k.castSucc.rev.val := by
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega
      rw [jacquetRectangleLeftArray_fixed x i _ (by omega), ite_eq_right (by omega), u.property.1 hk]

private theorem rightArray_eq (p : E × Z) :
    jacquetRectangleRightArray (rectangleReindex rightEntryEquiv p) =
      (weylLong m ℂ).val * rectangularJoin ((upperEntryCoordinates m).symm p.1).val.val p.2 := by
  let u : U := (upperEntryCoordinates m).symm p.1
  let y := rectangleReindex rightEntryEquiv p
  ext i j
  rw [weylLong_mul_matrix_apply]
  suffices h : ∀ k : I, jacquetRectangleRightArray y k.rev j = rectangularJoin u.val.val p.2 k j by
    simpa only [Fin.rev_rev, y, u] using h i.rev
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hi : ¬i.rev.val + (Fin.last m).val < m := by
      change ¬i.rev.val + m < m
      omega
    rw [rectangularJoin_last, jacquetRectangleRightArray_free y i.rev _ hi]
    exact rectangleReindex_apply rightEntryEquiv p (.inr i)
  · rw [rectangularJoin_castSucc]
    rcases lt_trichotomy i j with hj | rfl | hj
    · have h : ¬i.rev.val + j.castSucc.val < m := by
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega
      rw [jacquetRectangleRightArray_free y i.rev _ h, upperEntryCoordinates_symm_upper p.1 hj]
      exact rectangleReindex_apply rightEntryEquiv p (.inl ⟨(i, j), hj⟩)
    · have h : i.rev.val + i.castSucc.val + 1 = m := by
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega
      rw [jacquetRectangleRightArray_fixed y i.rev _ (by omega), ite_eq_left h, u.property.2 i]
    · have h : i.rev.val + j.castSucc.val + 1 < m := by
        simp only [Fin.val_rev, Fin.val_castSucc]
        omega
      rw [jacquetRectangleRightArray_fixed y i.rev _ (by omega), ite_eq_right (by omega), u.property.1 hj]

private def simpleEntryIndex (i : Fin r) : J :=
  ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ⟩

private theorem simpleEntryIndex_injective : Function.Injective (simpleEntryIndex (r := r)) := by
  intro i j h
  exact Fin.castSucc_injective _ (congrArg (fun p : J => p.val.1) h)

private theorem sum_simpleEntry (f : E) :
    (∑ p : J, f p * (if p.val.2.val = p.val.1.val + 1 then (1 : ℂ) else 0)) =
      ∑ i : Fin r, f (simpleEntryIndex i) := by
  classical
  have hsets : Finset.univ.filter (fun p : J => p.val.2.val = p.val.1.val + 1) =
      Finset.univ.image simpleEntryIndex := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      have hj := p.val.2.isLt
      let i : Fin r := ⟨p.val.1.val, by omega⟩
      refine ⟨i, Subtype.ext (Prod.ext ?_ ?_)⟩
      · apply Fin.ext
        rfl
      · apply Fin.ext
        simp only [simpleEntryIndex, Fin.val_succ, i]
        omega
    · rintro ⟨i, rfl⟩
      simp only [simpleEntryIndex, Fin.val_castSucc, Fin.val_succ]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hsets]
  exact Finset.sum_image (fun _ _ _ _ h => simpleEntryIndex_injective h)

private theorem leftOffset_simple (p : J) :
    jacquetRectangleRightOffset m (leftEntryEquiv (.inl p)) =
      if p.val.2.val = p.val.1.val + 1 then 1 else 0 := by
  change (if p.val.1.val + p.val.2.castSucc.rev.val + 1 = m then (1 : ℂ) else 0) = _
  have hj := p.val.2.isLt
  have he : p.val.1.val + p.val.2.castSucc.rev.val + 1 = m ↔
      p.val.2.val = p.val.1.val + 1 := by
    simp only [Fin.val_rev, Fin.val_castSucc]
    omega
  simp only [he]

private theorem rightOffset_simple (p : J) :
    jacquetRectangleLeftOffset m (rightEntryEquiv (.inl p)) =
      if p.val.2.val = p.val.1.val + 1 then 1 else 0 := by
  change (if p.val.1.rev.val + p.val.2.castSucc.val = m then (1 : ℂ) else 0) = _
  have hi := p.val.1.isLt
  have he : p.val.1.rev.val + p.val.2.castSucc.val = m ↔
      p.val.2.val = p.val.1.val + 1 := by
    simp only [Fin.val_rev, Fin.val_castSucc]
    omega
  simp only [he]

private theorem leftOffset_lastColumn (i : I) :
    jacquetRectangleRightOffset m (leftEntryEquiv (.inr i)) =
      if i = Fin.last r then 1 else 0 := by
  change (if i.val + (0 : Fin (m + 1)).val + 1 = m then (1 : ℂ) else 0) = _
  have he : i.val + (0 : Fin (m + 1)).val + 1 = m ↔ i = Fin.last r := by
    simp only [Fin.val_zero, add_zero, Fin.ext_iff, Fin.val_last]
    omega
  simp only [he]

private theorem rightOffset_lastColumn (i : I) :
    jacquetRectangleLeftOffset m (rightEntryEquiv (.inr i)) =
      if i = Fin.last r then 1 else 0 := by
  change (if i.rev.val + (Fin.last m).val = m then (1 : ℂ) else 0) = _
  have hi := i.isLt
  have he : i.rev.val + (Fin.last m).val = m ↔ i = Fin.last r := by
    simp only [Fin.val_rev, Fin.val_last, Fin.ext_iff]
    omega
  simp only [he]

private def jacquetRectanglePhase (p : E × Z) : ℂ :=
  p.2 (Fin.last r) + ∑ i : Fin r, p.1 (simpleEntryIndex i)

private theorem leftArray_phase (p : E × Z) :
    complexCoordinatePair (rectangleReindex leftEntryEquiv p) (jacquetRectangleRightOffset m) =
      jacquetRectanglePhase p := by
  unfold complexCoordinatePair
  rw [← leftEntryEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [rectangleReindex_apply, Sum.elim_inl, Sum.elim_inr, leftOffset_simple, leftOffset_lastColumn]
  rw [sum_simpleEntry]
  simp [jacquetRectanglePhase, mul_ite, add_comm]

private theorem rightArray_phase (p : E × Z) :
    complexCoordinatePair (jacquetRectangleLeftOffset m) (rectangleReindex rightEntryEquiv p) =
      jacquetRectanglePhase p := by
  unfold complexCoordinatePair
  rw [← rightEntryEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [rectangleReindex_apply, Sum.elim_inl, Sum.elim_inr, rightOffset_simple, rightOffset_lastColumn]
  simp_rw [mul_comm (ite _ _ _), sum_simpleEntry p.1]
  simp [jacquetRectanglePhase, mul_ite, add_comm]

private theorem jacquetRectanglePhase_eq (p : E × Z) :
    jacquetRectanglePhase p =
      p.2 (Fin.last r) + unipotentFourierSum r ((upperEntryCoordinates m).symm p.1) := by
  unfold jacquetRectanglePhase unipotentFourierSum
  apply congrArg (p.2 (Fin.last r) + ·)
  apply Finset.sum_congr rfl
  intro i _
  exact (upperEntryCoordinates_symm_upper p.1 Fin.castSucc_lt_succ).symm

/-- Evaluate a rectangular test on an upper-unipotent block and one free
column, with the additive character on the simple roots and last coordinate. -/
def complexJacquetRectangleKernel (a : ℂˣ) (f : R → ℂ) (p : U × Z) : ℂ :=
  f (rectangularJoin p.1.val.val p.2) *
    traceCharacter a (p.2 (Fin.last r) + unipotentFourierSum r p.1)

/-- The Fourier identity of Jacquet's Lemma 7.1 in actual unipotent
coordinates, for one common choice of Haar measure on the unipotent group. -/
theorem integral_complexJacquetRectangle_unipotent (a : ℂˣ) (Φ : SchwartzMap R ℂ)
    (μ : Measure U) [μ.IsHaarMeasure] :
    let ν := complexCoordinateMeasure I a
    let f := complexJacquetRectangleKernel (-a) (fun X => Φ (X * (weylLong (m + 1) ℂ).val))
    let g := complexJacquetRectangleKernel a (fun X =>
      rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure a) Φ
        ((weylLong m ℂ).val * X))
    Integrable f (μ.prod ν) ∧ Integrable g (μ.prod ν) ∧
      (∫ u, ∫ z, f (u, z) ∂ν ∂μ) = ∫ u, ∫ z, g (u, z) ∂ν ∂μ := by
  let ν := complexCoordinateMeasure I a
  let f := complexJacquetRectangleKernel (-a) (fun X => Φ (X * (weylLong (m + 1) ℂ).val))
  let g := complexJacquetRectangleKernel a (fun X =>
    rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure a) Φ
      ((weylLong m ℂ).val * X))
  change Integrable f (μ.prod ν) ∧ Integrable g (μ.prod ν) ∧ _
  let νE := complexCoordinateMeasure J a
  let e : E ≃ᵐ U := (upperEntryCoordinates m).symm.toMeasurableEquiv
  let ep : E × Z ≃ᵐ U × Z := e.prodCongr (MeasurableEquiv.refl Z)
  let : LocallyCompactSpace U := (upperEntryCoordinates m (K := ℂ)).isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology U := (upperEntryCoordinates m (K := ℂ)).secondCountableTopology
  have hprod : (νE.prod ν).map ep = (νE.map e).prod ν := by
    change (νE.prod ν).map (Prod.map e id) = _
    simpa only [Measure.map_id] using
      (Measure.map_prod_map νE ν e.measurable measurable_id).symm
  let fL := fun x : L → ℂ => Φ (jacquetRectangleLeftArray x) *
    traceCharacter a (-complexCoordinatePair x (jacquetRectangleRightOffset m))
  let gD := fun y : D → ℂ =>
    rectangularFourierIntegral (complexScaledCharacter (-a)) (complexSelfDualMeasure a) Φ
      (jacquetRectangleRightArray y) *
        traceCharacter a (complexCoordinatePair (jacquetRectangleLeftOffset m) y)
  have hfL : fL ∘ rectangleReindex leftEntryEquiv = f ∘ ep := by
    funext p
    simp only [Function.comp_apply, fL, f, complexJacquetRectangleKernel, leftArray_eq,
      leftArray_phase, jacquetRectanglePhase_eq, traceCharacter_neg_scale]
    rfl
  have hgD : gD ∘ rectangleReindex rightEntryEquiv = g ∘ ep := by
    funext p
    simp only [Function.comp_apply, gD, g, complexJacquetRectangleKernel, rightArray_eq,
      rightArray_phase, jacquetRectanglePhase_eq]
    rfl
  obtain ⟨hg, hf, heq⟩ := integral_complexJacquetRectangle_affine a Φ
  change Integrable gD _ at hg
  change Integrable fL _ at hf
  change (∫ y, gD y ∂complexCoordinateMeasure D a) =
    ∫ x, fL x ∂complexCoordinateMeasure L a at heq
  have hL := measurePreserving_rectangleReindex a (leftEntryEquiv (r := r))
  have hD := measurePreserving_rectangleReindex a (rightEntryEquiv (r := r))
  have hfcoord := hL.integrable_comp_of_integrable hf
  have hgcoord := hD.integrable_comp_of_integrable hg
  rw [hfL] at hfcoord
  rw [hgD] at hgcoord
  have hscalar : ∃ c : ℝ≥0, μ = c • νE.map e := by
    let ν₀ := complexSelfDualMeasure a
    let : ν₀.measure.IsAddHaarMeasure := ν₀.isAddHaar
    let μ₀ := νE.map e
    let : μ₀.IsHaarMeasure := upperEntryProductMeasure_isHaar ν₀
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul μ μ₀⟩
  obtain ⟨c, hc⟩ := hscalar
  have hfmap := (ep.measurableEmbedding.integrable_map_iff).mpr hfcoord
  have hgmap := (ep.measurableEmbedding.integrable_map_iff).mpr hgcoord
  rw [hprod] at hfmap hgmap
  have hν : μ.prod ν = c • (νE.map e).prod ν := by
    rw [hc, Measure.prod_smul_left]
  have hfμ : Integrable f (μ.prod ν) := hν.symm ▸ hfmap.smul_measure_nnreal
  have hgμ : Integrable g (μ.prod ν) := hν.symm ▸ hgmap.smul_measure_nnreal
  refine ⟨hfμ, hgμ, ?_⟩
  change (∫ u, ∫ z, f (u, z) ∂ν ∂μ) = ∫ u, ∫ z, g (u, z) ∂ν ∂μ
  rw [← integral_prod f hfμ, ← integral_prod g hgμ, hν]
  simp only [integral_smul_nnreal_measure, ← hprod, ep.measurableEmbedding.integral_map]
  congr 1
  change (∫ p, (f ∘ ep) p ∂νE.prod ν) = ∫ p, (g ∘ ep) p ∂νE.prod ν
  rw [← hfL, ← hgD]
  exact (hL.integral_comp (rectangleReindex leftEntryEquiv).toHomeomorph.measurableEmbedding fL).trans
    (heq.symm.trans (hD.integral_comp
      (rectangleReindex rightEntryEquiv).toHomeomorph.measurableEmbedding gD).symm)

end Langlands.GodementJacquet
