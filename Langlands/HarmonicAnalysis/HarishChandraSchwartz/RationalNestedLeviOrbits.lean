import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalNestedLeviNormalization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardParabolicExtension
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitConjugation
import Langlands.Representation.Parabolic.FlattenedTensorOccurrences
import Langlands.Representation.Plancherel.FormalDegreePullbackProof

/-! # Actual inducing orbits for a nested semistandard parabolic -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift

open RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p r : SemistandardSpectralIndex i} {m : LeviModel p}
  {SM : CommGroupScheme (Spec (CommRingCat.of F))} {iM : SM.toGrp ⟶ m.scheme}
  {q : SemistandardSpectralIndex iM} (h : RationalSemistandardParabolicLift p m q r)
  (mq : LeviModel q) (mr : LeviModel r)

local instance nestedOrbitAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

local instance nestedOrbitFiniteType (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

set_option hygiene false in
local notation "pointEquiv" => h.finalLeviPointsEquiv mq

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The point map for the orbit comparison is the literal final-Levi
map of the nested Fourier evaluation. -/
theorem finalLeviPointsEquiv_eq_leviEquiv :
    (pointEquiv) = h.leviEquiv h.innerLeviPointsEquiv := by
  apply ContinuousMulEquiv.ext
  intro x
  apply Subtype.ext
  rw [h.finalLeviPointsEquiv_coe]
  rfl

omit [LocallyOfFiniteType G.X.hom] in
private theorem liftedNormCharacters : (h.liftedLeviModel mq).normCharacters =
    fun χ => (mq.normCharacters χ).comp (pointEquiv).symm.toMonoidHom := by
  funext χ
  apply MonoidHom.ext
  intro x
  let L := h.liftedLeviModel mq
  change (rationalNormCharacters L.scheme χ).toMul (L.pointHomeomorph.symm x) =
    (rationalNormCharacters L.scheme χ).toMul
      (mq.pointHomeomorph.symm (mq.pointHomeomorph (L.pointHomeomorph.symm x)))
  exact congrArg (fun y => (rationalNormCharacters L.scheme χ).toMul y)
    (mq.pointHomeomorph.symm_apply_apply (L.pointHomeomorph.symm x)).symm

private theorem unitaryCharacter_subgroup_eq :
    unitaryUnramifiedCharacters
        (fun χ => (mq.normCharacters χ).comp (pointEquiv).symm.toMonoidHom) =
      unitaryUnramifiedCharacters mr.normCharacters := by
  rw [← liftedNormCharacters h mq]
  exact (h.liftedLeviModel mq).unitaryCharacters_eq mr

/-- The actual unitary unramified parameters transport by the inverse
final-Levi point map. -/
def finalLeviUnitaryCharacterEquiv : unitaryUnramifiedCharacters mq.normCharacters ≃ₜ*
    unitaryUnramifiedCharacters mr.normCharacters :=
  (unitaryUnramifiedCharactersHomeomorph (pointEquiv) mq.normCharacters).trans
    (RepresentedParabolic.subgroupCongrContinuous (unitaryCharacter_subgroup_eq h mq mr))

variable {A B : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : A.toGrp ⟶ mq.scheme) (ha : IsSplitComponent a)
  (b : B.toGrp ⟶ mr.scheme) (hb : IsSplitComponent b)

set_option hygiene false in
local notation "CQ" => mq.splitCenter a
set_option hygiene false in
local notation "CR" => mr.splitCenter b
set_option hygiene false in
local notation "hCQ" => mq.splitCenter_le_center a ha
set_option hygiene false in
local notation "hCR" => mr.splitCenter_le_center b hb

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
include ha hb in
private theorem finalLeviSplitCenter_map_symm : (CR).map (pointEquiv).symm.toMonoidHom = CQ :=
  (Subgroup.map_symm_eq_iff_map_eq (e := (pointEquiv).toMulEquiv) CQ).mpr
    (h.finalLeviSplitCenter_map mq mr a b ha hb)

set_option hygiene false in
local notation "hmap" => finalLeviSplitCenter_map_symm h mq mr a ha b hb

variable [(mq.splitCenter a).Normal] [(mr.splitCenter b).Normal]
  [MeasurableSpace (levi q ⧸ mq.splitCenter a)] [BorelSpace (levi q ⧸ mq.splitCenter a)]
  [MeasurableSpace (levi r ⧸ mr.splitCenter b)] [BorelSpace (levi r ⧸ mr.splitCenter b)]
  (muQ : Measure (levi q ⧸ mq.splitCenter a)) (muR : Measure (levi r ⧸ mr.splitCenter b))
  [muQ.IsHaarMeasure] [muR.IsHaarMeasure]
  (hmu : Measure.map (h.finalLeviQuotientEquiv mq mr a b ha hb) muQ = muR)

include hmu in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [muQ.IsHaarMeasure] [muR.IsHaarMeasure] in
private theorem finalLeviQuotientHaar_map_symm :
    Measure.map (quotientContinuousMulEquiv (pointEquiv).symm CQ CR hmap) muR = muQ := by
  let E := h.finalLeviQuotientEquiv mq mr a b ha hb
  have hinv : quotientContinuousMulEquiv (pointEquiv).symm CQ CR hmap = E.symm := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    apply E.injective
    rw [E.apply_symm_apply, quotientContinuousMulEquiv_mk]
    change QuotientGroup.mk ((pointEquiv) ((pointEquiv).symm y)) = QuotientGroup.mk y
    rw [ContinuousMulEquiv.apply_symm_apply]
  rw [hinv, ← hmu]
  exact MeasurableEquiv.map_map_symm E.symm.toHomeomorph.toMeasurableEquiv

set_option hygiene false in
local notation "liftClass" => DiscreteSeriesClass.pullback (pointEquiv).symm CQ hCQ CR hCR hmap
  muQ muR (finalLeviQuotientHaar_map_symm h mq mr a ha b hb muQ muR hmu)

/-- The actual spectral orbit on the final inner Levi gives one ambient
orbit for the lifted parabolic. -/
def liftedOrbitClass : OrbitClass.{u, uV} mq a ha muQ → OrbitClass.{u, uV} mr b hb muR :=
  Quotient.map (liftClass) (by
    rintro ω ω' ⟨χ, hχ⟩
    have hsmul : (liftClass) (χ • ω') =
        h.finalLeviUnitaryCharacterEquiv mq mr χ • (liftClass) ω' := by
      apply Subtype.ext
      exact SmoothDualClass.pullback_twist (pointEquiv).symm _ _ _ _
    exact ⟨h.finalLeviUnitaryCharacterEquiv mq mr χ, hsmul.symm.trans (congrArg (liftClass) hχ)⟩)

set_option hygiene false in
local notation "innerRep" => orbitRepresentative mq a ha muQ
set_option hygiene false in
local notation "ambientRep" => orbitRepresentative mr b hb muR
set_option hygiene false in
local notation "outerOrbit" => h.liftedOrbitClass mq mr a ha b hb muQ muR hmu

variable [muQ.IsInvInvariant] [muR.IsInvInvariant]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
/-- Each actual inner inducing object has an ambient representative in
the one lifted orbit, with the same formal degree at the matched Haar. -/
theorem liftedOrbitClass_match (dq : CompactData q) (dr : CompactData r)
    (O : OrbitClass.{u, uV} mq a ha muQ)
    (π : UnitaryOrbitRepresentative mq.normCharacters ((innerRep) O)) :
    ∃ ρ : UnitaryOrbitRepresentative mr.normCharacters ((ambientRep) ((outerOrbit) O)),
      Nonempty ((SmoothRep.pullback (pointEquiv) ρ.val.obj).representation.Equiv π.val.obj.representation) ∧
      semistandardOrbitFormalDegree q mq dq ((innerRep) O) CQ hCQ muQ
          (orbitRepresentative_isSquareIntegrable mq a ha muQ O) π =
        semistandardOrbitFormalDegree r mr dr ((ambientRep) ((outerOrbit) O)) CR hCR muR
          (orbitRepresentative_isSquareIntegrable mr b hb muR ((outerOrbit) O)) ρ := by
  let squareπ := unitaryOrbitRepresentative_isDiscreteSeries mq.normCharacters ((innerRep) O)
    CQ hCQ muQ (orbitRepresentative_isSquareIntegrable mq a ha muQ O) π
  let ω := discreteSeriesClass CQ hCQ muQ π.val squareπ
  have hO : (Quotient.mk _ ω : OrbitClass.{u, uV} mq a ha muQ) = O := by
    obtain ⟨χ, hχ⟩ := π.property
    apply Eq.trans _ (mk_discreteSeriesClass_orbitRepresentative mq a ha muQ O)
    apply Quotient.sound
    exact ⟨χ, Subtype.ext hχ⟩
  let ρ := IrreducibleAdmissibleRep.pullback (pointEquiv).symm π.val
  have squareρ : IsSquareIntegrableModCentralSubgroup CR hCR ρ.obj.representation muR :=
    (isSquareIntegrableModCentralSubgroup_comp_iff (pointEquiv).symm CQ hCQ CR hCR hmap muQ muR
      (finalLeviQuotientHaar_map_symm h mq mr a ha b hb muQ muR hmu) π.val.obj.representation).mpr
      squareπ
  have hr : (Quotient.mk _ (discreteSeriesClass CR hCR muR ρ squareρ) :
      OrbitClass.{u, uV} mr b hb muR) = (outerOrbit) O :=
    congrArg (outerOrbit) hO
  let R := orbitRepresentativeMember mr b hb muR ((outerOrbit) O) ρ squareρ hr
  refine ⟨R, ⟨SmoothRep.equivOfIso (SmoothRep.pullbackSymmIso (pointEquiv).symm π.val.obj)⟩, ?_⟩
  exact representationFormalDegree_pullback (pointEquiv).symm CQ hCQ CR hCR hmap muQ muR
    (finalLeviQuotientHaar_map_symm h mq mr a ha b hb muQ muR hmu)
    (compactOpenCofinal q dq) (compactOpenCofinal r dr) squareπ π.val.property.1 squareρ ρ.property.1

end Langlands.HarishChandraSchwartz.RationalSemistandardParabolicLift
