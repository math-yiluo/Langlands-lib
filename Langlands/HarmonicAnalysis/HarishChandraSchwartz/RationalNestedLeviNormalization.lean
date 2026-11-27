import Langlands.GroupScheme.Rational.RootProductTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardNestedFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceQuotientHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSplitCenterIndependenceProof

/-! # The common final Levi in the nested Fourier diagram -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General Langlands.Plancherel
open Langlands.Plancherel.WaldspurgerSourceNormalization

namespace Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift

open RationalSemistandard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p r : SemistandardSpectralIndex i} {m : LeviModel p}
  {SM : CommGroupScheme (Spec (CommRingCat.of F))} {iM : SM.toGrp ⟶ m.scheme}
  {q : SemistandardSpectralIndex iM} (h : RationalSemistandardParabolicLift p m q r)
  (mq : LeviModel q)

/-- The inner Levi model represents the final Levi of the lifted parabolic
by composition with the actual outer Levi inclusion. -/
def liftedLeviModel : LeviModel r where
  scheme := mq.scheme
  inclusion := mq.inclusion ≫ m.inclusion
  represents := h.levi_image ▸ mq.represents.comp m.represents
  closed := mq.closed.comp m.closed
  reductive := mq.reductive

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance nestedLeviAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom :=
  m.reductive.isAffineHom

local instance nestedLeviFiniteType (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

/-- Identify the two final Levi point groups by the common scheme model. -/
def finalLeviPointsEquiv : levi q ≃ₜ* levi r :=
  mq.pointHomeomorph.symm.trans (h.liftedLeviModel mq).pointHomeomorph

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem finalLeviPointsEquiv_coe (x : levi q) :
    (h.finalLeviPointsEquiv mq x : rationalPoints G) =
      rationalPoints.map m.inclusion (x : rationalPoints m.scheme) := by
  change rationalPoints.map (mq.inclusion ≫ m.inclusion) (mq.pointHomeomorph.symm x) = _
  rw [RationalPointFamily.rationalPoints_map_comp_apply]
  congr 1
  exact congrArg Subtype.val (mq.pointHomeomorph.apply_symm_apply x)

variable (mr : LeviModel r)

/-- Norm characters on the final ambient Levi pull back to the algebraic
norm characters on the inner Levi, under the actual model isomorphism. -/
theorem finalLevi_normCharacters (χ : rationalCharacters mr.scheme) :
    (mr.normCharacters χ).comp (h.finalLeviPointsEquiv mq).toMonoidHom =
      mq.normCharacters ((h.liftedLeviModel mq).characterEquiv mr χ) := by
  apply MonoidHom.ext
  intro x
  change mr.normCharacters χ (h.finalLeviPointsEquiv mq x) = _
  rw [← (h.liftedLeviModel mq).normCharacters_characterEquiv mr χ]
  let L := h.liftedLeviModel mq
  let chiPull := L.characterEquiv mr χ
  exact congrArg (fun y => (rationalNormCharacters L.scheme chiPull).toMul y)
    (L.pointHomeomorph.symm_apply_apply (mq.pointHomeomorph.symm x))

variable {A B : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : A.toGrp ⟶ mq.scheme) (b : B.toGrp ⟶ mr.scheme)
  (ha : IsSplitComponent a) (hb : IsSplitComponent b)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
include ha hb in
/-- The literal split-center point subgroups of the final Levi agree under
the same point identification. -/
theorem finalLeviSplitCenter_map :
    (mq.splitCenter a).map (h.finalLeviPointsEquiv mq).toMonoidHom = mr.splitCenter b := by
  rw [← splitCenterChoiceIndependence r (h.liftedLeviModel mq) mr A B a b ha hb]
  unfold LeviModel.splitCenter
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact congrArg (h.liftedLeviModel mq).pointHomeomorph
    (mq.pointHomeomorph.symm_apply_apply x)

variable [(mq.splitCenter a).Normal] [(mr.splitCenter b).Normal]
  [MeasurableSpace (levi q ⧸ mq.splitCenter a)] [BorelSpace (levi q ⧸ mq.splitCenter a)]
  [MeasurableSpace (levi r ⧸ mr.splitCenter b)] [BorelSpace (levi r ⧸ mr.splitCenter b)]

/-- The induced isomorphism on the two split-central point quotients. -/
def finalLeviQuotientEquiv : (levi q ⧸ mq.splitCenter a) ≃ₜ* (levi r ⧸ mr.splitCenter b) :=
  quotientContinuousMulEquiv (h.finalLeviPointsEquiv mq) (mr.splitCenter b) (mq.splitCenter a)
    (h.finalLeviSplitCenter_map mq mr a b ha hb)

/-- If the compact on the outer Levi is the trace of the ambient compact,
then the source quotient measures have the same normalization on the final Levi. -/
theorem finalLevi_sourceQuotientHaar_map
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (KM : OpenSubgroup (rationalPoints m.scheme))
    (hKMc : IsCompact (KM : Set (rationalPoints m.scheme)))
    (hKM : ∀ x : rationalPoints m.scheme, x ∈ KM ↔ rationalPoints.map m.inclusion x ∈ K) :
    Measure.map (h.finalLeviQuotientEquiv mq mr a b ha hb)
        (mq.sourceQuotientHaar a KM hKMc) = mr.sourceQuotientHaar b K hK := by
  let : LocallyCompactSpace (levi r) := (isClosed_levi_of_model mr).locallyCompactSpace
  let : LocallyCompactSpace (levi q) := (isClosed_levi_of_model mq).locallyCompactSpace
  let : SecondCountableTopology (levi r) := TopologicalSpace.Subtype.secondCountableTopology _
  let e := h.finalLeviQuotientEquiv mq mr a b ha hb
  let : (Measure.map e (mq.sourceQuotientHaar a KM hKMc)).IsHaarMeasure :=
    e.isHaarMeasure_map _
  let L := K.comap (levi r).subtype continuous_subtype_val
  let LM := KM.comap (levi q).subtype continuous_subtype_val
  apply IsNormalizedQuotientHaar.eq_of_haar (mr.splitCenter b) L _ _ _
    (mr.sourceQuotientHaar_normalized b K hK)
  refine (normalizedQuotientHaar_map_iff (mr.splitCenter b) L (mq.splitCenter a) LM
    (h.finalLeviPointsEquiv mq) (h.finalLeviSplitCenter_map mq mr a b ha hb) ?_
    (mq.sourceQuotientHaar a KM hKMc)).2 (mq.sourceQuotientHaar_normalized a KM hKMc)
  intro x
  change (h.finalLeviPointsEquiv mq x : rationalPoints G) ∈ K ↔
    (x : rationalPoints m.scheme) ∈ KM
  rw [h.finalLeviPointsEquiv_coe]
  exact (hKM x).symm

end Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift
