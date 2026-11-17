import Langlands.Geometry.Analytic.GroundFieldExtensionCounterexample.Charts
import Langlands.Geometry.Analytic.RationalSpectrumAtlas
import Langlands.Geometry.Analytic.AtlasSubatlas
import Langlands.Geometry.Analytic.AffinoidSpectrumAtlas
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentationProof
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # A strong atlas map twisted by Frobenius on some target charts

The source is the spectrum of `F₄ × F₄` with its one-chart atlas.  The target is
the spectrum of `F₄⁴` with the rational charts that lie in `leftDomain` (the
points of the first three factors) or in `rightDomain` (the points of factors
`0`, `1` and `3`), excluding those charts that contain the image of the source
and lie in both.  The continuous map is induced by `restrictMap`.  On a target
chart contained in `rightDomain` the pullback is the factorization of
`restrictMap` composed with Frobenius; on every other chart it is the
factorization itself.  Frobenius fixes every point of the source spectrum, so
this is a `StrongHom` over `F₂`.
-/

noncomputable section

namespace Langlands.Analytic.GroundFieldExtensionCounterexample

open Set Topology CategoryTheory
open scoped Topology
open PresentedAffinoidAlgebra AffinoidAtlasPresentation

/-! ### Rational domains of the target spectrum -/

/-- The idempotent of `F₄⁴` supported on the factor `p`. -/
def idempotent (p : Fin 4) : TargetRing := Pi.single p 1

theorem idempotent_apply (p k : Fin 4) : idempotent p k = if k = p then 1 else 0 :=
  Pi.single_apply p 1 k

/-- The rational chart `{y | y (ι a) ≤ 1/2}` of the target spectrum, where `ι`
is `targetInclusion`. -/
def upperChart (a : TargetRing) : RationalChart F₂ targetAlgebra :=
  RationalChart.upperBound (targetInclusion a) (1 / 2) (by norm_num)

/-- Since every point takes only the values `0` and `1`, the locus of
`upperChart a` is the vanishing locus of `ι a`. -/
theorem mem_upperChart_locus (a : TargetRing) (y : BanachSpectrum targetAlgebra) :
    y ∈ (upperChart a).locus ↔ y (targetInclusion a) = 0 := by
  rw [upperChart, RationalChart.mem_locus_upperBound]
  rcases target_apply_eq_zero_or_one y (targetInclusion a) with h | h <;> rw [h] <;> norm_num

/-- The points of the first three factors: the vanishing locus of `ι (idempotent 3)`. -/
def leftDomain : Set (BanachSpectrum targetAlgebra) := (upperChart (idempotent 3)).locus

/-- The points of the factors `0`, `1`, `3`: the vanishing locus of `ι (idempotent 2)`. -/
def rightDomain : Set (BanachSpectrum targetAlgebra) := (upperChart (idempotent 2)).locus

/-- The points of the factor `p`: the vanishing locus of `ι (1 - idempotent p)`. -/
def pointDomain (p : Fin 4) : Set (BanachSpectrum targetAlgebra) :=
  (upperChart (1 - idempotent p)).locus

/-- The image of the source spectrum in the target spectrum. -/
def sourceImage : Set (BanachSpectrum targetAlgebra) :=
  Set.range (BanachSpectrum.comap restrictMap.toBoundedRingHom)

theorem comap_restrictMap_apply (x : BanachSpectrum sourceAlgebra) (a : TargetRing) :
    BanachSpectrum.comap restrictMap.toBoundedRingHom x (targetInclusion a) =
      x (sourceInclusion (restrict a)) := by
  change x (restrictMap (targetInclusion a)) = _
  rw [restrictMap_targetInclusion]

theorem restrict_idempotent (p : Fin 4) (hp : 2 ≤ (p : ℕ)) :
    restrict (idempotent p) = 0 := by
  funext i
  have hne : Fin.castLE (by norm_num) i ≠ p := by
    intro h
    have h1 := congrArg Fin.val h
    rw [Fin.val_castLE] at h1
    have := i.isLt
    omega
  simp [restrict_apply, idempotent_apply, hne]

theorem sourceImage_subset_upperChart (p : Fin 4) (hp : 2 ≤ (p : ℕ)) :
    sourceImage ⊆ (upperChart (idempotent p)).locus := by
  rintro _ ⟨x, rfl⟩
  rw [mem_upperChart_locus, comap_restrictMap_apply, restrict_idempotent p hp, map_zero,
    map_zero]

theorem sourceImage_subset_leftDomain : sourceImage ⊆ leftDomain :=
  sourceImage_subset_upperChart 3 (by decide)

theorem sourceImage_subset_rightDomain : sourceImage ⊆ rightDomain :=
  sourceImage_subset_upperChart 2 (by decide)

theorem idempotent_mul_one_sub (p q : Fin 4) (h : p ≠ q) :
    idempotent p * (1 - idempotent q) = idempotent p := by
  funext k
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, idempotent_apply]
  by_cases hk : k = p
  · subst hk
    simp [h]
  · simp [hk]

theorem pointDomain_subset_upperChart (p q : Fin 4) (h : q ≠ p) :
    pointDomain p ⊆ (upperChart (idempotent q)).locus := by
  intro y hy
  rw [pointDomain, mem_upperChart_locus] at hy
  rw [mem_upperChart_locus, ← idempotent_mul_one_sub q p h, map_mul, map_mul, hy, mul_zero]

theorem pointDomain_subset_left_or_right (p : Fin 4) :
    pointDomain p ⊆ leftDomain ∨ pointDomain p ⊆ rightDomain := by
  by_cases hp : p = 3
  · subst hp
    exact Or.inr (pointDomain_subset_upperChart 3 2 (by decide))
  · exact Or.inl (pointDomain_subset_upperChart p 3 (Ne.symm hp))

theorem not_sourceImage_subset_pointDomain (p : Fin 4) : ¬sourceImage ⊆ pointDomain p := by
  obtain ⟨q, hq⟩ : ∃ q : Fin 2, Fin.castLE (by norm_num : 2 ≤ 4) q ≠ p := by
    revert p
    decide
  intro h
  have hmem := h ⟨sourcePoint q, rfl⟩
  rw [pointDomain, mem_upperChart_locus, comap_restrictMap_apply,
    sourcePoint_sourceInclusion] at hmem
  simp [restrict_apply, idempotent_apply, hq] at hmem

theorem exists_mem_pointDomain (y : BanachSpectrum targetAlgebra) :
    ∃ p, y ∈ pointDomain p := by
  have h0 : (∏ p : Fin 4, (1 - idempotent p)) = 0 := by
    funext k
    rw [Finset.prod_apply, Pi.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [idempotent_apply])
  have hy : y (targetInclusion (∏ p : Fin 4, (1 - idempotent p))) = 0 := by
    rw [h0, map_zero, map_zero]
  rw [map_prod, map_prod] at hy
  obtain ⟨p, -, hp⟩ := Finset.prod_eq_zero_iff.mp hy
  exact ⟨p, (mem_upperChart_locus _ y).mpr hp⟩

theorem mem_pointDomain_iff_lt (p : Fin 4) (y : BanachSpectrum targetAlgebra) :
    y ∈ pointDomain p ↔ y (targetInclusion (1 - idempotent p)) < 1 / 2 := by
  rw [pointDomain, mem_upperChart_locus]
  rcases target_apply_eq_zero_or_one y (targetInclusion (1 - idempotent p)) with h | h <;>
    rw [h] <;> norm_num

theorem isOpen_pointDomain (p : Fin 4) : IsOpen (pointDomain p) := by
  have h : pointDomain p = {y | BanachSpectrum.evaluation
      (targetInclusion (1 - idempotent p)) y < 1 / 2} := by
    ext y
    exact mem_pointDomain_iff_lt p y
  rw [h]
  exact isOpen_lt (ContinuousMap.continuous _) continuous_const

/-! ### The target atlas -/

/-- The rational charts selected for the target atlas: those contained in
`leftDomain` or in `rightDomain`, except those that both contain the source
image and lie in `leftDomain ∩ rightDomain`. -/
def IsSelected (i : RationalSpectrumAtlas.Index F₂ targetAlgebra) : Prop :=
  (i.val ⊆ leftDomain ∨ i.val ⊆ rightDomain) ∧
    ¬(sourceImage ⊆ i.val ∧ i.val ⊆ leftDomain ∩ rightDomain)

theorem isSelected_of_subset_pointDomain (i : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (p : Fin 4) (h : i.val ⊆ pointDomain p) : IsSelected i := by
  refine ⟨?_, fun h' => not_sourceImage_subset_pointDomain p (h'.1.trans h)⟩
  rcases pointDomain_subset_left_or_right p with hp | hp
  · exact Or.inl (h.trans hp)
  · exact Or.inr (h.trans hp)

theorem range_atlas_chart (i : (RationalSpectrumAtlas.atlas targetAlgebra).Index) :
    Set.range ((RationalSpectrumAtlas.atlas targetAlgebra).chart i) = i.val :=
  RationalSpectrumAtlas.range_chart i

/-- The selected charts refine every rational chart near each of its points:
near a point of the factor `p`, intersect with `pointDomain p`. -/
theorem isLocallyRefiningSelection :
    (RationalSpectrumAtlas.atlas targetAlgebra).IsLocallyRefiningSelection IsSelected := by
  rintro _ ⟨i, rfl⟩ y hy
  beta_reduce at hy ⊢
  rw [range_atlas_chart] at hy
  obtain ⟨p, hp⟩ := exists_mem_pointDomain y
  let d : (RationalSpectrumAtlas.atlas targetAlgebra).Index :=
    RationalSpectrumAtlas.Index.inter i (RationalSpectrumAtlas.Index.ofChart (upperChart (1 - idempotent p)))
  have hd : d.val = i.val ∩ pointDomain p := RationalSpectrumAtlas.Index.val_inter _ _
  refine ⟨{Set.range ((RationalSpectrumAtlas.atlas targetAlgebra).chart d)},
    Set.finite_singleton _, ?_, ?_, ?_⟩
  · rw [Set.singleton_subset_iff]
    exact ⟨⟨d, isSelected_of_subset_pointDomain d p (by rw [hd]; exact inter_subset_right)⟩,
      rfl⟩
  · intro V hV
    rw [Set.mem_singleton_iff] at hV
    subst hV
    rw [range_atlas_chart, range_atlas_chart, hd]
    exact ⟨inter_subset_left, hy, hp⟩
  · rw [Set.sUnion_singleton, range_atlas_chart, range_atlas_chart, hd]
    exact inter_mem_nhdsWithin _ ((isOpen_pointDomain p).mem_nhds hp)

/-- The target: the selected rational charts on the spectrum of `F₄⁴`. -/
def targetAtlasPresentation : AffinoidAtlasPresentation.{0, 0, 0} F₂ :=
  AffinoidAtlasPresentation.subpresentation
    ⟨TopCat.of (BanachSpectrum targetAlgebra), RationalSpectrumAtlas.atlas targetAlgebra⟩
    IsSelected isLocallyRefiningSelection

/-- The source: the spectrum of `F₄ × F₄` with its one-chart atlas. -/
def sourceAtlasPresentation : AffinoidAtlasPresentation.{0, 0, 0} F₂ :=
  PresentedAffinoidSpace.atlasPresentation (Opposite.op sourceAlgebra)

/-! ### The twisted strong map -/

/-- The continuous map of spectra induced by `restrictMap`. -/
def weakBaseMap : C(sourceAtlasPresentation.space, targetAtlasPresentation.space) :=
  BanachSpectrum.comapContinuous restrictMap.toBoundedRingHom

theorem image_weakBaseMap (i : sourceAtlasPresentation.atlas.Index) :
    weakBaseMap '' Set.range (sourceAtlasPresentation.atlas.chart i) = sourceImage := by
  change BanachSpectrum.comapContinuous restrictMap.toBoundedRingHom '' Set.range _root_.id =
    sourceImage
  rw [Set.range_id, Set.image_univ]
  rfl

theorem range_targetAtlasPresentation_chart (j : targetAtlasPresentation.atlas.Index) :
    Set.range (targetAtlasPresentation.atlas.chart j) = j.val.val :=
  RationalSpectrumAtlas.range_chart j.val

theorem val_subset_of_range_subset (j j' : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (h : Set.range (RationalSpectrumAtlas.chart j) ⊆ Set.range (RationalSpectrumAtlas.chart j')) :
    j.val ⊆ j'.val := by
  rwa [RationalSpectrumAtlas.range_chart, RationalSpectrumAtlas.range_chart] at h

theorem admissible_iff (i : sourceAtlasPresentation.atlas.Index)
    (j : targetAtlasPresentation.atlas.Index) :
    weakBaseMap '' Set.range (sourceAtlasPresentation.atlas.chart i) ⊆
        Set.range (targetAtlasPresentation.atlas.chart j) ↔
      sourceImage ⊆ j.val.val := by
  rw [image_weakBaseMap, range_targetAtlasPresentation_chart]
  exact Iff.rfl

theorem hasImageIn_of_subset (j : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (h : sourceImage ⊆ j.val) : HasImageIn F₂ restrictMap j.presentation.locus := by
  intro x
  rw [RationalSpectrumAtlas.Index.locus_presentation]
  exact h ⟨x, rfl⟩

/-- The unique factorization of `restrictMap` through a rational chart containing
the source image. -/
def factor (j : RationalSpectrumAtlas.Index F₂ targetAlgebra) (h : sourceImage ⊆ j.val) :
    BoundedAlgHom F₂ j.presentation.algebra sourceAlgebra :=
  (j.presentation.existsUnique_factorization sourceAlgebra restrictMap
    (hasImageIn_of_subset j h)).exists.choose

theorem factor_comp_baseMap (j : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (h : sourceImage ⊆ j.val) : (factor j h).comp j.presentation.baseMap = restrictMap :=
  (j.presentation.existsUnique_factorization sourceAlgebra restrictMap
    (hasImageIn_of_subset j h)).exists.choose_spec

theorem factor_eq_of_comp_baseMap (j : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (h : sourceImage ⊆ j.val) (ψ : BoundedAlgHom F₂ j.presentation.algebra sourceAlgebra)
    (hψ : ψ.comp j.presentation.baseMap = restrictMap) : ψ = factor j h :=
  (j.presentation.existsUnique_factorization sourceAlgebra restrictMap
    (hasImageIn_of_subset j h)).unique hψ (factor_comp_baseMap j h)

theorem factor_restriction (j j' : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (hj : Set.range (RationalSpectrumAtlas.chart j) ⊆ Set.range (RationalSpectrumAtlas.chart j'))
    (h : sourceImage ⊆ j.val) (h' : sourceImage ⊆ j'.val) :
    (factor j h).comp (RationalSpectrumAtlas.restriction j j' hj) = factor j' h' := by
  apply factor_eq_of_comp_baseMap
  rw [BoundedAlgHom.comp_assoc, RationalSpectrumAtlas.restriction_comp_baseMap,
    factor_comp_baseMap]

open Classical in
/-- The pullback on a target chart: twisted by Frobenius exactly when the chart
lies in `rightDomain`. -/
def weakPullback (j : RationalSpectrumAtlas.Index F₂ targetAlgebra) (h : sourceImage ⊆ j.val) :
    BoundedAlgHom F₂ j.presentation.algebra sourceAlgebra :=
  if j.val ⊆ rightDomain then frobenius.comp (factor j h) else factor j h

theorem weakPullback_of_subset (j : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (h : sourceImage ⊆ j.val) (hj : j.val ⊆ rightDomain) :
    weakPullback j h = frobenius.comp (factor j h) := by
  simp [weakPullback, hj]

theorem weakPullback_of_not_subset (j : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (h : sourceImage ⊆ j.val) (hj : ¬j.val ⊆ rightDomain) :
    weakPullback j h = factor j h := by
  simp [weakPullback, hj]

theorem apply_frobenius (x : BanachSpectrum sourceAlgebra) (s : sourceAlgebra) :
    x (frobenius s) = x s :=
  congrArg (fun y : BanachSpectrum sourceAlgebra => y s) (comap_frobenius x)

theorem apply_weakPullback_baseMap (j : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (h : sourceImage ⊆ j.val) (x : BanachSpectrum sourceAlgebra) (a : targetAlgebra) :
    x (weakPullback j h (j.presentation.baseMap a)) = x (restrictMap a) := by
  have hf : factor j h (j.presentation.baseMap a) = restrictMap a :=
    congrArg (fun φ : BoundedAlgHom F₂ targetAlgebra sourceAlgebra => φ a)
      (factor_comp_baseMap j h)
  by_cases hj : j.val ⊆ rightDomain
  · rw [weakPullback_of_subset j h hj, BoundedAlgHom.comp_apply, apply_frobenius, hf]
  · rw [weakPullback_of_not_subset j h hj, hf]

/-- Twisting is constant along an inclusion of admissible selected charts: if a
smaller chart lay in `rightDomain` and a larger selected one did not, the larger
one would lie in `leftDomain`, and the smaller one would be excluded. -/
theorem subset_rightDomain_iff (j j' : RationalSpectrumAtlas.Index F₂ targetAlgebra)
    (hsel : IsSelected j) (hsel' : IsSelected j') (hjj' : j.val ⊆ j'.val)
    (h : sourceImage ⊆ j.val) : j.val ⊆ rightDomain ↔ j'.val ⊆ rightDomain := by
  constructor
  · intro hj
    by_contra hj'
    have hleft : j'.val ⊆ leftDomain := hsel'.1.resolve_right hj'
    exact hsel.2 ⟨h, subset_inter (hjj'.trans hleft) hj⟩
  · intro hj'
    exact hjj'.trans hj'

/-- The Frobenius-twisted strong atlas map over `F₂`. -/
def weakMap : StrongHom sourceAtlasPresentation targetAtlasPresentation where
  baseMap := weakBaseMap
  target_exists i := by
    refine ⟨⟨RationalSpectrumAtlas.Index.ofChart (upperChart (idempotent 3)), ?_⟩, ?_⟩
    · refine ⟨Or.inl Subset.rfl, ?_⟩
      rintro ⟨-, hsub⟩
      have hmem : targetPoint 2 ∈ (upperChart (idempotent 3)).locus := by
        rw [mem_upperChart_locus, targetPoint_targetInclusion, idempotent_apply]
        simp
      have hright := (hsub hmem).2
      rw [rightDomain, mem_upperChart_locus, targetPoint_targetInclusion,
        idempotent_apply] at hright
      simp at hright
    · exact (admissible_iff i _).mpr sourceImage_subset_leftDomain
  pullback i j h := weakPullback j.val ((admissible_iff i j).mp h)
  chart_comm i j h x := by
    apply BanachSpectrum.ext
    intro a
    exact apply_weakPullback_baseMap j.val ((admissible_iff i j).mp h) x a
  restriction_comm i i' j j' hi hj h h' := by
    have hs : sourceImage ⊆ j.val.val := (admissible_iff i j).mp h
    have hs' : sourceImage ⊆ j'.val.val := (admissible_iff i' j').mp h'
    have hjj' : j.val.val ⊆ j'.val.val := val_subset_of_range_subset j.val j'.val hj
    change (weakPullback j'.val hs') =
      (weakPullback j.val hs).comp (RationalSpectrumAtlas.restriction j.val j'.val hj)
    have hfac := factor_restriction j.val j'.val hj hs hs'
    by_cases hr : j.val.val ⊆ rightDomain
    · have hr' : j'.val.val ⊆ rightDomain :=
        (subset_rightDomain_iff j.val j'.val j.property j'.property hjj' hs).mp hr
      rw [weakPullback_of_subset _ _ hr, weakPullback_of_subset _ _ hr',
        BoundedAlgHom.comp_assoc, hfac]
    · have hr' : ¬j'.val.val ⊆ rightDomain := fun hr' =>
        hr ((subset_rightDomain_iff j.val j'.val j.property j'.property hjj' hs).mpr hr')
      rw [weakPullback_of_not_subset _ _ hr, weakPullback_of_not_subset _ _ hr', hfac]

end Langlands.Analytic.GroundFieldExtensionCounterexample
