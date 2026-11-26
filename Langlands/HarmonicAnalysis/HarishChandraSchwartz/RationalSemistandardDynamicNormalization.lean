import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupQuotientHaar
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Plancherel.ActualConjugateLeviCoherenceStatement
import Langlands.Representation.Plancherel.SquareIntegrableCentralPullback

/-! # Intrinsic quotient Haar in the dynamic Levi normalization -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.CocharacterPresentation

open DynamicOppositeStandardIntertwining ActualConjugateLeviCoherence SourceDensity

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p) (m : LeviModel p)
  {Z : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : Z.toGrp ⟶ m.scheme) (ha : IsSplitComponent a)

set_option hygiene false in
local notation "M" => DynamicOppositeStandardIntertwining.levi r.hom
set_option hygiene false in
local notation "C" => m.splitCenter a
set_option hygiene false in
local notation "e" => r.literalLeviHomeomorph
set_option hygiene false in
local notation "D" => (C).comap (e).toMonoidHom

include ha in
set_option maxHeartbeats 600000 in
private theorem isActualSplitCenter_comap : ActualCommonLeviV3.IsActualSplitCenter r.hom D := by
  let b := a ≫ (parameterIso m r).inv
  refine ⟨Z, b, ha.comp_iso (parameterIso m r).symm, ?_⟩
  rw [← MonoidHom.range_comp]
  ext x
  change e x ∈ C ↔ _
  rw [LeviModel.splitCenter, ← MonoidHom.range_comp]
  change (∃ y, m.pointHomeomorph (rationalPoints.map a y) = e x) ↔
    (∃ y, parameterHomeomorph r.hom (rationalPoints.map b y) = x)
  refine exists_congr fun y => ?_
  rw [← (e).injective.eq_iff, ← pointHomeomorph_map_parameterIso]
  unfold b
  rw [← RationalPointFamily.rationalPoints_map_comp_apply, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

variable [(C).Normal] [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
  (mu : Measure (levi p ⧸ C)) [mu.IsHaarMeasure]

local instance : LocallyCompactSpace (levi p) :=
  (isClosed_levi_of_model (chosenLeviModel p)).locallyCompactSpace
local instance : LocallyCompactSpace M := (levi_isClosed r.hom).locallyCompactSpace
local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩
local instance : MeasurableSpace (M ⧸ D) := borel (M ⧸ D)
local instance : BorelSpace (M ⧸ D) := ⟨rfl⟩

include ha in
set_option maxHeartbeats 600000 in
private theorem pullbackMeasure_isInvInvariant :
    (centralSubgroupPullbackMeasure e C mu).IsInvInvariant := by
  let : IsAffine m.scheme.X.left :=
    letI := m.reductive.isAffineHom
    isAffine_of_isAffineHom m.scheme.X.hom
  have hC : IsClosed (C : Set (levi p)) :=
    m.pointHomeomorph.toHomeomorph.isClosedMap _ (isClosed_range_splitComponent m.scheme a ha)
  have hD : IsClosed (D : Set M) := hC.preimage (e).continuous
  let : IsClosed (D : Set M) := hD
  let : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  have hmod (x : M) : Measure.modularCharacter x = 1 :=
    (modularCharacter_continuousMulEquiv e x).symm.trans (levi_modularCharacter m (e x))
  let measure := centralSubgroupPullbackMeasure e C mu
  let : measure.IsMulRightInvariant := Haar.centralSubgroupQuotient_isMulRightInvariant D
    (centralSubgroup_comap_le_center e C (m.splitCenter_le_center a ha)) hD hmod measure
  exact Langlands.isInvInvariant_of_isMulRightInvariant measure

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (hsq : IsSquareIntegrableModCentralSubgroup C (m.splitCenter_le_center a ha)
    π.obj.representation mu)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
/-- The intrinsic inducing representation and split-central quotient Haar
transport to the dynamic Levi through the literal point identification. -/
def leviNormalization : LeviNormalization r.hom (SmoothRep.pullback e π.obj) where
  center := D
  central := centralSubgroup_comap_le_center e C (m.splitCenter_le_center a ha)
  normal := inferInstance
  quotientMeasurable := inferInstance
  quotientBorel := inferInstance
  quotientMeasure := centralSubgroupPullbackMeasure e C mu
  quotientHaar := inferInstance
  quotientInversion := pullbackMeasure_isInvInvariant r m a ha mu
  splitCenter := isActualSplitCenter_comap r m a ha
  squareIntegrable := isSquareIntegrableModCentralSubgroup_pullback e C mu
    (m.splitCenter_le_center a ha) π.obj.representation hsq
  irreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.obj.representation e).mpr π.property.1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 900000 in
/-- The quotient isomorphism carries the dynamic measure back to exactly the
supplied intrinsic Haar scale. -/
theorem leviNormalization_matches :
    let L := r.leviNormalization m a ha mu π hsq
    ∃ hcenter : L.center.map (e).toMonoidHom = C,
      L.quotientMeasure.map (quotientContinuousMulEquiv e C L.center hcenter) = mu := by
  exact ⟨Subgroup.map_comap_eq_self_of_surjective (e).surjective C,
    centralSubgroupPullbackMeasure_map e C mu⟩

end Langlands.HarishChandraSchwartz.RationalSemistandard.CocharacterPresentation
