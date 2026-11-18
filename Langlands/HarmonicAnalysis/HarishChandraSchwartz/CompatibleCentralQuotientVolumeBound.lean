import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.LatticeQuotientVolumeBound
import Langlands.Analysis.Local.QuotientMass
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Compact cell bounds for the supplied compatible central quotient measure -/

noncomputable section

universe u

open MeasureTheory
open scoped ENNReal Pointwise
open Langlands.HarishChandraSchwartz

namespace Langlands.QuotientIntegration

section Topology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Left translation commutes with the same-representative quotient map. -/
theorem leftQuotientMap_image_smul (A : Subgroup G) [A.Normal] (g : G) (D : Set G) :
    leftQuotientMap A '' (g • D) =
      quotientLeftTranslate A g '' (leftQuotientMap A '' D) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    exact ⟨leftQuotientMap A y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨g * y, Set.mem_smul_set.mpr ⟨y, hy, rfl⟩, rfl⟩

/-- An open subgroup covers every compact set by finitely many left cosets. -/
theorem exists_finset_leftCoset_cover (K : OpenSubgroup G) {Y : Set G}
    (hY : IsCompact Y) :
    ∃ t : Finset G, Y ⊆ ⋃ c ∈ t, c • (K : Set G) := by
  classical
  apply hY.elim_finite_subcover (fun c => c • (K : Set G))
    (fun c => K.isOpen.smul c)
  intro y _
  exact Set.mem_iUnion.mpr ⟨y, Set.mem_smul_set.mpr ⟨1, K.one_mem, mul_one y⟩⟩

end Topology

section Measure

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} [A.Normal] (hA : IsClosed (A : Set G))
  (hAc : A ≤ Subgroup.center G)
  [MeasurableSpace A] [BorelSpace A]
  {muG : Measure G} [muG.IsMulLeftInvariant]
  {muA : Measure A} [muA.IsHaarMeasure] [muA.Regular] [muA.IsMulRightInvariant]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {muQ : Measure (LeftQuotient A)} (hQ : IsCompatible A muG muA muQ)

include hA hAc hQ in
/-- Every image of a left translate has its original mass for the supplied
compatible measure. No Haar measure on a different quotient is chosen. -/
theorem IsCompatible.measure_image_quotientLeftTranslate (g : G)
    (D : Set (LeftQuotient A)) :
    muQ (quotientLeftTranslate A g '' D) = muQ D := by
  calc
    _ = (muQ.map (quotientLeftTranslate A g)) (quotientLeftTranslate A g '' D) := by
      rw [hQ.map_quotientLeftTranslate hA hAc]
    _ = muQ D := by
      rw [(quotientLeftTranslate A g).measurableEmbedding.map_apply,
        Set.preimage_image_eq D (quotientLeftTranslate A g).injective]

include hA hAc hQ in
/-- The mass of an actual quotient double coset is at most the original
finite double-coset index times the mass of the identity compact-open orbit. -/
theorem IsCompatible.measure_image_doubleCoset_le (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) :
    muQ (leftQuotientMap A '' DoubleCoset.doubleCoset g K.toSubgroup K.toSubgroup) ≤
      (doubleCosetIndex K.toSubgroup g : ℝ≥0∞) * muQ (compactOpenQuotientOrbit A K) := by
  classical
  have hfin := doubleCosetIndex_ne_zero_of_compact_open K hK g
  let : ((conjSubgroup g K.toSubgroup).subgroupOf K.toSubgroup).FiniteIndex := ⟨hfin⟩
  let : Fintype (K.toSubgroup ⧸ (conjSubgroup g K.toSubgroup).subgroupOf K.toSubgroup) :=
    Fintype.ofFinite _
  rw [doubleCoset_eq_iUnion, Set.image_iUnion]
  refine (measure_iUnion_le _).trans_eq ?_
  simp_rw [leftQuotientMap_image_smul,
    hQ.measure_image_quotientLeftTranslate hA hAc]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [doubleCosetIndex, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

include hA hAc hQ in
/-- Compact right factors increase quotient-cell volumes by a uniform constant.
The cell need not be measurable for this outer-measure bound. -/
theorem IsCompatible.exists_measure_compact_cell_le_index (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) {Y : Set G} (hY : IsCompact Y) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : G,
      muQ (leftQuotientMap A '' ((K : Set G) * {g} * Y)) ≤
        ENNReal.ofReal (C * (doubleCosetIndex K.toSubgroup g : ℝ)) := by
  classical
  obtain ⟨t, ht⟩ := exists_finset_leftCoset_cover K hY
  let m := muQ (compactOpenQuotientOrbit A K)
  have hm : m ≠ ⊤ := (hQ.compactOpenQuotientOrbit_mass K hK).2.ne
  let n : ℕ := ∑ c ∈ t, doubleCosetIndex K.toSubgroup c
  let C : ℝ := (n : ℝ) * m.toReal
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C + 1, by positivity, fun g => ?_⟩
  have hsub : (K : Set G) * {g} * Y ⊆
      ⋃ c ∈ t, DoubleCoset.doubleCoset (g * c) K.toSubgroup K.toSubgroup := by
    rintro x ⟨z, ⟨k, hk, _, rfl, rfl⟩, y, hy, rfl⟩
    obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.mp (ht hy)
    obtain ⟨k', hk', rfl⟩ := Set.mem_smul_set.mp hyc
    exact Set.mem_iUnion₂.mpr ⟨c, hc, DoubleCoset.mem_doubleCoset.mpr
      ⟨k, hk, k', hk', by simp only [smul_eq_mul]; group⟩⟩
  have hmul (c : G) :
      (doubleCosetIndex K.toSubgroup (g * c) : ℝ≥0∞) ≤
        (doubleCosetIndex K.toSubgroup g : ℝ≥0∞) *
          (doubleCosetIndex K.toSubgroup c : ℝ≥0∞) := by
    exact_mod_cast ((doubleCosetIndexBounds.{u,u} G K.toSubgroup).1 g c
      (doubleCosetIndex_ne_zero_of_compact_open K hK g)
      (doubleCosetIndex_ne_zero_of_compact_open K hK c)).2
  calc
    _ ≤ muQ (⋃ c ∈ t, leftQuotientMap A ''
        DoubleCoset.doubleCoset (g * c) K.toSubgroup K.toSubgroup) := by
      simpa only [Set.image_iUnion] using measure_mono (Set.image_mono hsub)
    _ ≤ ∑ c ∈ t, muQ (leftQuotientMap A ''
        DoubleCoset.doubleCoset (g * c) K.toSubgroup K.toSubgroup) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ t, ((doubleCosetIndex K.toSubgroup g : ℝ≥0∞) *
        (doubleCosetIndex K.toSubgroup c : ℝ≥0∞)) * m := by
      apply Finset.sum_le_sum
      intro c _
      exact (hQ.measure_image_doubleCoset_le hA hAc K hK (g * c)).trans
        (mul_le_mul_left (hmul c) m)
    _ = (doubleCosetIndex K.toSubgroup g : ℝ≥0∞) * (n : ℝ≥0∞) * m := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Nat.cast_sum]
    _ = ENNReal.ofReal (C * (doubleCosetIndex K.toSubgroup g : ℝ)) := by
      rw [show C * (doubleCosetIndex K.toSubgroup g : ℝ) =
        (doubleCosetIndex K.toSubgroup g : ℝ) * (n : ℝ) * m.toReal by dsimp [C]; ring,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

end Measure

end Langlands.QuotientIntegration


open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- A uniform positive volume constant for the compact cells of the
split-central quotient, with growth given by the double-coset index. -/
def RationalSplitCentralCellIndexBound
    {F : Type u} [Field F] [TopologicalSpace F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range))
    (K : OpenSubgroup (rationalPoints G)) (Y : Set (rationalPoints G)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
    muQ (leftQuotientMap (rationalPoints.map s).range ''
      ((K : Set (rationalPoints G)) * {g} * Y)) ≤
      ENNReal.ofReal (C * (doubleCosetIndex K.toSubgroup g : ℝ))

/-- Compact cells on the actual split-central quotient have the finite-index
volume bound for the same supplied compatible quotient measure. -/
theorem exists_rationalSplitCentralQuotient_measure_compact_cell_le_index
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
    [MeasurableSpace (rationalPoints.map s).range]
    [BorelSpace (rationalPoints.map s).range]
    [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    [BorelSpace (LeftQuotient (rationalPoints.map s).range)]
    {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant]
    {muA : Measure (rationalPoints.map s).range} [muA.IsHaarMeasure]
    [muA.IsMulRightInvariant]
    {muQ : Measure (LeftQuotient (rationalPoints.map s).range)}
    (hQ : IsCompatible (rationalPoints.map s).range muG muA muQ)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    {Y : Set (rationalPoints G)} (hY : IsCompact Y) :
    RationalSplitCentralCellIndexBound s muQ K Y := by
  have hAc := hs.isCentralSplitTorus.isCentral.range_le_center
  let := (rationalPoints.map s).range.normal_of_le_center hAc
  let : IsClosedImmersion s.hom.hom.left := hs.isCentralSplitTorus.isSplitSubtorus.2
  let : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom s.hom.hom.left
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology F T.toGrp.X
  have hA : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) :=
    (isClosedEmbedding_rationalPointMap F s.hom.hom).isClosed_range
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  have : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  have : LocallyCompactSpace (rationalPoints.map s).range := hA.locallyCompactSpace
  have : SecondCountableTopology (rationalPoints.map s).range :=
    inferInstanceAs (SecondCountableTopology
      ((rationalPoints.map s).range : Set (rationalPoints G)))
  have : muA.Regular := inferInstance
  exact hQ.exists_measure_compact_cell_le_index hA hAc K hK hY

end Langlands.HarishChandraSchwartz
