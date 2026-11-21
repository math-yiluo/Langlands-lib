import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket

/-! # The split-central quotient Haar scale in semistandard Weyl comparison -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.Plancherel.WaldspurgerSourceNormalization

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure

open ActualConjugateLeviCoherence (LeviNormalization)

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  {a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme}
  {ha : ∀ p, IsSplitComponent (a p)}
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  {mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p))}
  [∀ p, (mu p).IsHaarMeasure]
  {d : ∀ p : SemistandardSpectralIndex i, CompactData p}
  {hG : IsConnectedReductive G}

set_option hygiene false in
set_option quotPrecheck false in
local notation "Center" p:max => (chosenLeviModel p).splitCenter (a p)

variable (a mu d) in
/-- The synthesis and form use mass one on the image of the same compact
Levi trace in each actual split-central quotient. -/
def IntrinsicQuotientNormalization : Prop :=
  ∀ p, IsNormalizedQuotientHaar (Center p)
    ((d p).compact.comap (levi p).subtype continuous_subtype_val) (mu p)

variable (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (t : RationalSemistandardTheta.{u, uV} a ha mu)

set_option hygiene false in
set_option quotPrecheck false in
local notation "r" => C.presentation t.1
set_option hygiene false in
set_option quotPrecheck false in
local notation "D" => C.normalization t

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))] in
/-- The dynamic split center in the actual comparison maps to the split
center used by the intrinsic packet and form. -/
theorem comparisonCenter_map :
    (D).center.map (r).literalLeviHomeomorph.toMonoidHom = Center t.1 := by
  obtain ⟨A, b, hb, h⟩ := (D).splitCenter
  rw [h, Subgroup.map_map]
  refine Eq.trans ?_ (splitCenterChoiceIndependence t.1 (r).leviModel (chosenLeviModel t.1)
    A (Z t.1) b (a t.1) hb (ha t.1))
  unfold LeviModel.splitCenter
  rfl

/-- The literal quotient isomorphism from the normalization in the
intertwiner to the normalization in the integral. -/
def comparisonQuotientHomeomorph :
    (_ ⧸ (D).center) ≃ₜ* (levi t.1 ⧸ Center t.1) :=
  quotientContinuousMulEquiv (r).literalLeviHomeomorph (Center t.1) (D).center
    (comparisonCenter_map C t)

local instance (p : SemistandardSpectralIndex i) : LocallyCompactSpace (levi p) :=
  (isClosed_levi_of_model (chosenLeviModel p)).locallyCompactSpace

local instance (p : SemistandardSpectralIndex i) : SecondCountableTopology (levi p) :=
  letI : SecondCountableTopology (rationalPoints G) := rationalPoint_secondCountableTopology F G
  TopologicalSpace.Subtype.secondCountableTopology (levi p : Set (rationalPoints G))

/-- The absolute source scale identifies the comparison Haar measure
with the actual measure used by the intrinsic source integrals. -/
theorem comparisonQuotientHaar_map (hn : IntrinsicQuotientNormalization a mu d) :
    Measure.map (comparisonQuotientHomeomorph C t) (D).quotientMeasure = mu t.1 := by
  let e := comparisonQuotientHomeomorph C t
  let : (Measure.map e (D).quotientMeasure).IsHaarMeasure :=
    e.isHaarMeasure_map (D).quotientMeasure
  let L := (d t.1).compact.comap (levi t.1).subtype continuous_subtype_val
  apply IsNormalizedQuotientHaar.eq_of_haar (Center t.1) L _ _ _ (hn t.1)
  exact (normalizedQuotientHaar_map_iff (Center t.1) L (D).center _
    (r).literalLeviHomeomorph (comparisonCenter_map C t) (fun _ => Iff.rfl)
    (D).quotientMeasure).mpr (C.sourceNormalization t).2

variable (q : SemistandardSpectralIndex i) (n : C.Lift t q)

set_option hygiene false in
set_option quotPrecheck false in
local notation "hc" => InvariantComparison.liftConjugatesLevi (C.centralizer_le t.1) (d t.1).compact n

/-- The quotient homeomorphism for the same inverse Levi conjugation
used on the actual inducing representatives. -/
def weylQuotientHomeomorph : (levi q ⧸ Center q) ≃ₜ* (levi t.1 ⧸ Center t.1) :=
  Association.quotientLeviConjugationSymm hc (chosenLeviModel t.1) (chosenLeviModel q)
    (a t.1) (ha t.1) (a q) (ha q)

/-- Compact Weyl lifts preserve the normalized quotient Haar measure.
The equality uses the source traces and the literal split-center images. -/
theorem weylQuotientHaar_map (hn : IntrinsicQuotientNormalization a mu d) :
    Measure.map (weylQuotientHomeomorph C t q n) (mu q) = mu t.1 := by
  let e := Association.leviPointConjugation hc
  let E := weylQuotientHomeomorph C t q n
  let : (Measure.map E (mu q)).IsHaarMeasure := E.isHaarMeasure_map (mu q)
  let L := (d t.1).compact.comap (levi t.1).subtype continuous_subtype_val
  let L' := (d q).compact.comap (levi q).subtype continuous_subtype_val
  have hcenter : (Center q).map e.symm.toMonoidHom = Center t.1 :=
    (Subgroup.map_symm_eq_iff_map_eq (e := e.toMulEquiv) (Center t.1)).mpr
      (Association.splitCenter_map_leviPointConjugation hc (chosenLeviModel t.1)
        (chosenLeviModel q) (a t.1) (ha t.1) (a q) (ha q))
  have htrace (x : levi q) : e.symm x ∈ L ↔ x ∈ L' := by
    let g : rationalPoints G := n.val
    have h := RationalDynamicSource.mem_conjugateCompact g
      (e.symm x : rationalPoints G) (d t.1).compact
    have he : g * (e.symm x : rationalPoints G) * g⁻¹ = (x : rationalPoints G) :=
      (Association.leviPointConjugation_apply hc (e.symm x)).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply x))
    rw [he, RationalDynamicSource.conjugateCompact_eq_self g _ n.property.1] at h
    change (e.symm x : rationalPoints G) ∈ (d t.1).compact ↔
      (x : rationalPoints G) ∈ (d q).compact
    exact h.symm.trans (by rw [C.sameCompact t.1 q])
  apply IsNormalizedQuotientHaar.eq_of_haar (Center t.1) L _ _ _ (hn t.1)
  exact (normalizedQuotientHaar_map_iff (Center t.1) L (Center q) L' e.symm hcenter htrace
    (mu q)).mpr (hn q)

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceMeasure
