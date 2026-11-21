import Langlands.Geometry.Analytic.GroundFieldExtensionCounterexample.NonExtensionStatement

/-! # Proof that the Frobenius-twisted strong map does not extend to `F₄` -/

noncomputable section

namespace Langlands.Analytic.GroundFieldExtensionCounterexample

open Set AffinoidAtlasPresentation
open PresentedAffinoidAlgebra.GroundFieldExtension

/-! ### Charts of the target atlas -/

theorem targetPoint_mem_upperChart_iff (p q : Fin 4) :
    targetPoint p ∈ (upperChart (idempotent q)).locus ↔ p ≠ q := by
  rw [mem_upperChart_locus, targetPoint_targetInclusion, idempotent_apply]
  by_cases h : p = q <;> simp [h]

theorem not_leftDomain_subset_rightDomain : ¬leftDomain ⊆ rightDomain := fun h =>
  (targetPoint_mem_upperChart_iff 2 2).mp
    (h ((targetPoint_mem_upperChart_iff 2 3).mpr (by decide))) rfl

theorem not_rightDomain_subset_leftDomain : ¬rightDomain ⊆ leftDomain := fun h =>
  (targetPoint_mem_upperChart_iff 3 3).mp
    (h ((targetPoint_mem_upperChart_iff 3 2).mpr (by decide))) rfl

/-- The chart `leftDomain` of the target atlas. -/
def leftIndex : targetAtlasPresentation.atlas.Index :=
  ⟨RationalSpectrumAtlas.Index.ofChart (upperChart (idempotent 3)),
    ⟨Or.inl subset_rfl, fun h =>
      not_leftDomain_subset_rightDomain (h.2.trans inter_subset_right)⟩⟩

/-- The chart `rightDomain` of the target atlas. -/
def rightIndex : targetAtlasPresentation.atlas.Index :=
  ⟨RationalSpectrumAtlas.Index.ofChart (upperChart (idempotent 2)),
    ⟨Or.inr subset_rfl, fun h =>
      not_rightDomain_subset_leftDomain (h.2.trans inter_subset_left)⟩⟩

/-- The chart `pointDomain 0` of the target atlas. -/
def pointIndex : targetAtlasPresentation.atlas.Index :=
  ⟨RationalSpectrumAtlas.Index.ofChart (upperChart (1 - idempotent 0)),
    isSelected_of_subset_pointDomain _ 0 subset_rfl⟩

theorem admissible_leftIndex (i : sourceAtlasPresentation.atlas.Index) :
    weakMap.baseMap '' range (sourceAtlasPresentation.atlas.chart i) ⊆
      range (targetAtlasPresentation.atlas.chart leftIndex) :=
  (admissible_iff i leftIndex).mpr sourceImage_subset_leftDomain

theorem admissible_rightIndex (i : sourceAtlasPresentation.atlas.Index) :
    weakMap.baseMap '' range (sourceAtlasPresentation.atlas.chart i) ⊆
      range (targetAtlasPresentation.atlas.chart rightIndex) :=
  (admissible_iff i rightIndex).mpr sourceImage_subset_rightDomain

theorem pointIndex_subset_leftIndex :
    range (targetAtlasPresentation.atlas.chart pointIndex) ⊆
      range (targetAtlasPresentation.atlas.chart leftIndex) := by
  rw [range_targetAtlasPresentation_chart, range_targetAtlasPresentation_chart]
  exact pointDomain_subset_upperChart 0 3 (by decide)

theorem pointIndex_subset_rightIndex :
    range (targetAtlasPresentation.atlas.chart pointIndex) ⊆
      range (targetAtlasPresentation.atlas.chart rightIndex) := by
  rw [range_targetAtlasPresentation_chart, range_targetAtlasPresentation_chart]
  exact pointDomain_subset_upperChart 0 2 (by decide)

theorem weakPullback_comp_baseMap_of_not_subset
    (j : RationalSpectrumAtlas.Index F₂ targetAlgebra) (h : sourceImage ⊆ j.val)
    (hj : ¬j.val ⊆ rightDomain) :
    (weakPullback j h).comp j.presentation.baseMap = restrictMap := by
  rw [weakPullback_of_not_subset j h hj, factor_comp_baseMap]

theorem weakPullback_comp_baseMap_of_subset
    (j : RationalSpectrumAtlas.Index F₂ targetAlgebra) (h : sourceImage ⊆ j.val)
    (hj : j.val ⊆ rightDomain) :
    (weakPullback j h).comp j.presentation.baseMap = frobenius.comp restrictMap := by
  rw [weakPullback_of_subset j h hj, BoundedAlgHom.comp_assoc, factor_comp_baseMap]

theorem weakPullback_comp_baseMap_left (i : sourceAtlasPresentation.atlas.Index)
    (h : weakMap.baseMap '' range (sourceAtlasPresentation.atlas.chart i) ⊆
      range (targetAtlasPresentation.atlas.chart leftIndex)) :
    (weakMap.pullback i leftIndex h).comp leftIndex.val.presentation.baseMap =
      restrictMap := by
  exact weakPullback_comp_baseMap_of_not_subset leftIndex.val _
    not_leftDomain_subset_rightDomain

theorem weakPullback_comp_baseMap_right (i : sourceAtlasPresentation.atlas.Index)
    (h : weakMap.baseMap '' range (sourceAtlasPresentation.atlas.chart i) ⊆
      range (targetAtlasPresentation.atlas.chart rightIndex)) :
    (weakMap.pullback i rightIndex h).comp rightIndex.val.presentation.baseMap =
      frobenius.comp restrictMap := by
  exact weakPullback_comp_baseMap_of_subset rightIndex.val _
    (subset_rfl : rightDomain ⊆ rightDomain)

/-! ### A point of the extended source spectrum -/

/-- Evaluation of the extended source algebra at the first factor. -/
def extendedEvaluation : BoundedAlgHom F₄ (algebra F₂ F₄ sourceAlgebra) F₄ :=
  lift F₂ F₄ sourceAlgebra F₄ (sourceEvaluation 0)

/-- The point of the extended source spectrum given by `extendedEvaluation`. -/
def extendedPoint : BanachSpectrum (algebra F₂ F₄ sourceAlgebra) :=
  BanachSpectrum.comap extendedEvaluation.toBoundedRingHom (BanachSpectrum.fieldPoint F₄)

theorem extendedPoint_apply (s : algebra F₂ F₄ sourceAlgebra) :
    extendedPoint s = ‖extendedEvaluation s‖ := rfl

theorem extendedEvaluation_iota (a : sourceAlgebra) :
    extendedEvaluation (iota F₂ F₄ sourceAlgebra a) = sourceEvaluation 0 a :=
  lift_iota F₂ F₄ sourceAlgebra F₄ (sourceEvaluation 0) a

theorem spectrumProjection_extendedPoint :
    spectrumProjection F₂ F₄ sourceAlgebra extendedPoint = sourcePoint 0 := by
  apply BanachSpectrum.ext
  intro a
  change ‖extendedEvaluation (iota F₂ F₄ sourceAlgebra a)‖ = ‖sourceEvaluation 0 a‖
  rw [extendedEvaluation_iota]

theorem comap_restrictMap_sourcePoint_mem :
    BanachSpectrum.comap restrictMap.toBoundedRingHom (sourcePoint 0) ∈ pointDomain 0 := by
  rw [pointDomain, mem_upperChart_locus, comap_restrictMap_apply, sourcePoint_sourceInclusion]
  simp [restrict_apply, idempotent_apply]

/-! ### An element moved by the extended Frobenius -/

theorem card_F₂ : Fintype.card F₂ = 2 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (WithAbs.equiv trivialAbs₂).toEquiv,
    Nat.card_zmod]

theorem card_F₄ : Fintype.card F₄ = 4 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (WithAbs.equiv trivialAbs₄).toEquiv,
    GaloisField.card 2 2 (by norm_num)]
  norm_num

/-- Some element of `F₄` is not fixed by the Frobenius of `F₄` over `F₂`. -/
theorem exists_pow_card_ne : ∃ ω : F₄, ω ^ Fintype.card F₂ ≠ ω := by
  classical
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F₄)) (t := Finset.univ) (by
      rw [Finset.card_univ, card_F₄]
      exact (Finset.card_insert_le _ _).trans_lt (by simp))
  refine ⟨ω, fun h => hω ?_⟩
  rw [card_F₂] at h
  have h' : ω * (ω - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · simp [h0]
  · simp [sub_eq_zero.mp h1]

/-- The element `ι(ω e₀) - ω ι(e₀)` of the extended target algebra. -/
def testElement (ω : F₄) : algebra F₂ F₄ targetAlgebra :=
  iota F₂ F₄ targetAlgebra (targetInclusion (Pi.single 0 ω)) -
    ω • iota F₂ F₄ targetAlgebra (targetInclusion (idempotent 0))

theorem extendedEvaluation_restrict (a : TargetRing) :
    extendedEvaluation (map F₂ F₄ restrictMap (iota F₂ F₄ targetAlgebra (targetInclusion a))) =
      a 0 := by
  rw [map_iota, extendedEvaluation_iota, restrictMap_targetInclusion,
    sourceEvaluation_sourceInclusion, restrict_apply]
  rfl

theorem extendedEvaluation_frobenius_restrict (a : TargetRing) :
    extendedEvaluation (map F₂ F₄ frobenius
      (map F₂ F₄ restrictMap (iota F₂ F₄ targetAlgebra (targetInclusion a)))) =
        a 0 ^ Fintype.card F₂ := by
  rw [map_iota, map_iota, extendedEvaluation_iota, restrictMap_targetInclusion,
    frobenius_sourceInclusion, sourceEvaluation_sourceInclusion, Pi.pow_apply, restrict_apply]
  rfl

theorem extendedEvaluation_test (ω : F₄) :
    extendedEvaluation (map F₂ F₄ restrictMap (testElement ω)) = 0 := by
  unfold testElement
  rw [map_sub, map_smul, map_sub, map_smul, extendedEvaluation_restrict,
    extendedEvaluation_restrict]
  simp [idempotent_apply]

theorem extendedEvaluation_frobenius_test (ω : F₄) :
    extendedEvaluation (map F₂ F₄ frobenius (map F₂ F₄ restrictMap (testElement ω))) =
      ω ^ Fintype.card F₂ - ω := by
  unfold testElement
  rw [map_sub, map_smul, map_sub, map_smul, map_sub, map_smul,
    extendedEvaluation_frobenius_restrict, extendedEvaluation_frobenius_restrict]
  simp [idempotent_apply]

/-! ### The non-extension theorem -/


/-- If a strong map `F` between the extended presentations has the extended
pullback of `weakMap` on an admissible chart `j` containing `pointIndex`, then
its value at `extendedPoint` is the image of a point `w` of the extended
`pointIndex` chart, and `w` is computed by the pullback of `weakMap` on `j`. -/
theorem exists_point_of_extends
    (F : StrongHom (IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
        sourceAtlasPresentation.atlas)
      (IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
        targetAtlasPresentation.atlas))
    (i : sourceAtlasPresentation.atlas.Index) (j : targetAtlasPresentation.atlas.Index)
    (h : weakMap.baseMap '' range (sourceAtlasPresentation.atlas.chart i) ⊆
      range (targetAtlasPresentation.atlas.chart j))
    (hj : range (targetAtlasPresentation.atlas.chart pointIndex) ⊆
      range (targetAtlasPresentation.atlas.chart j))
    (hF : ∃ h', F.pullback i j h' = map F₂ F₄ (weakMap.pullback i j h)) :
    ∃ w : BanachSpectrum (algebra F₂ F₄ (targetAtlasPresentation.atlas.algebra pointIndex)),
      (IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
          targetAtlasPresentation.atlas).atlas.chart pointIndex w =
        F.baseMap ((IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
          sourceAtlasPresentation.atlas).atlas.chart i extendedPoint) ∧
      ∀ t : algebra F₂ F₄ targetAlgebra,
        w (map F₂ F₄ pointIndex.val.presentation.baseMap t) =
          extendedPoint
            (map F₂ F₄ ((weakMap.pullback i j h).comp j.val.presentation.baseMap) t) := by
  obtain ⟨h', hF'⟩ := hF
  have hu : BanachSpectrum.comap (map F₂ F₄ (weakMap.pullback i j h)).toBoundedRingHom
      extendedPoint ∈ range (BanachSpectrum.comap
        (IndexedAffinoidAtlas.GroundFieldExtension.restriction F₂ F₄
          targetAtlasPresentation.atlas pointIndex j hj).toBoundedRingHom) := by
    rw [IndexedAffinoidAtlas.GroundFieldExtension.mem_range_restriction_iff F₂ F₄ _]
    have hp := spectrumProjection_naturality (K := F₂) (L := F₄) (weakMap.pullback i j h)
      extendedPoint
    have hc := weakMap.chart_comm i j h
      (spectrumProjection F₂ F₄ (sourceAtlasPresentation.atlas.algebra i) extendedPoint)
    rw [hp, hc, range_targetAtlasPresentation_chart]
    have hmem := comap_restrictMap_sourcePoint_mem
    rw [← spectrumProjection_extendedPoint] at hmem
    exact hmem
  obtain ⟨w, hw⟩ := hu
  refine ⟨w, ?_, ?_⟩
  · have hc := F.chart_comm i j h' extendedPoint
    rw [hF'] at hc
    exact ((IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
      targetAtlasPresentation.atlas).atlas.restriction_chart pointIndex j
        ((IndexedAffinoidAtlas.GroundFieldExtension.range_chart_subset_iff F₂ F₄ _
          pointIndex j).2 hj) w).symm.trans
      ((congrArg ((IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
        targetAtlasPresentation.atlas).atlas.chart j) hw).trans hc)
  · intro t
    have hres : (targetAtlasPresentation.atlas.restriction pointIndex j hj).comp
        j.val.presentation.baseMap = pointIndex.val.presentation.baseMap :=
      RationalSpectrumAtlas.restriction_comp_baseMap pointIndex.val j.val hj
    have h1 : map F₂ F₄ (targetAtlasPresentation.atlas.restriction pointIndex j hj)
        (map F₂ F₄ j.val.presentation.baseMap t) =
          map F₂ F₄ pointIndex.val.presentation.baseMap t :=
      (congrArg (fun φ => φ t) (map_comp (K := F₂) (L := F₄)
        (targetAtlasPresentation.atlas.restriction pointIndex j hj)
        j.val.presentation.baseMap)).symm.trans (congrArg (fun φ => map F₂ F₄ φ t) hres)
    have h2 : map F₂ F₄ (weakMap.pullback i j h) (map F₂ F₄ j.val.presentation.baseMap t) =
        map F₂ F₄ ((weakMap.pullback i j h).comp j.val.presentation.baseMap) t :=
      (congrArg (fun φ => φ t) (map_comp (K := F₂) (L := F₄) (weakMap.pullback i j h)
        j.val.presentation.baseMap)).symm
    have hwt := congrArg
      (fun y : BanachSpectrum (algebra F₂ F₄ (targetAtlasPresentation.atlas.algebra j)) =>
        y (map F₂ F₄ j.val.presentation.baseMap t)) hw
    exact (congrArg (fun s => w s) h1).symm.trans
      (hwt.trans (congrArg (fun s => extendedPoint s) h2))

/-- The Frobenius-twisted strong map `weakMap` has no extension to `F₄`. -/
theorem nonExtension : NonExtensionStatement := by
  rintro ⟨F, hF⟩
  let i : sourceAtlasPresentation.atlas.Index := PUnit.unit
  obtain ⟨wL, hwL, htL⟩ := exists_point_of_extends F i leftIndex
    (admissible_leftIndex i) pointIndex_subset_leftIndex
    (hF i leftIndex (admissible_leftIndex i))
  obtain ⟨wR, hwR, htR⟩ := exists_point_of_extends F i rightIndex
    (admissible_rightIndex i) pointIndex_subset_rightIndex
    (hF i rightIndex (admissible_rightIndex i))
  have hw : wL = wR :=
    ((IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
      targetAtlasPresentation.atlas).atlas.isEmbedding_chart
        pointIndex).injective (hwL.trans hwR.symm)
  subst hw
  obtain ⟨ω, hω⟩ := exists_pow_card_ne
  have hL := congrArg (fun φ => extendedPoint (map F₂ F₄ φ (testElement ω)))
    (weakPullback_comp_baseMap_left i (admissible_leftIndex i))
  have hR := congrArg (fun φ => extendedPoint (map F₂ F₄ φ (testElement ω)))
    (weakPullback_comp_baseMap_right i (admissible_rightIndex i))
  have hfr := congrArg (fun φ => extendedPoint (φ (testElement ω)))
    (map_comp (K := F₂) (L := F₄) frobenius restrictMap)
  have ht : extendedPoint (map F₂ F₄ restrictMap (testElement ω)) =
      extendedPoint (map F₂ F₄ frobenius (map F₂ F₄ restrictMap (testElement ω))) :=
    hL.symm.trans (((htL (testElement ω)).symm.trans (htR (testElement ω))).trans
      (hR.trans hfr))
  change ‖extendedEvaluation (map F₂ F₄ restrictMap (testElement ω))‖ =
    ‖extendedEvaluation (map F₂ F₄ frobenius (map F₂ F₄ restrictMap (testElement ω)))‖ at ht
  rw [extendedEvaluation_test, extendedEvaluation_frobenius_test, norm_zero] at ht
  exact hω (sub_eq_zero.mp (norm_eq_zero.mp ht.symm))

end Langlands.Analytic.GroundFieldExtensionCounterexample
