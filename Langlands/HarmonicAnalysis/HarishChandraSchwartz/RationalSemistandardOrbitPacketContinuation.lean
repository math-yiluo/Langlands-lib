import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeightedSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitDensityFromOppositeContinuations
import Langlands.Representation.Plancherel.ActualOppositeFullDomainContinuationStatement
import Langlands.Representation.Plancherel.ActualConjugateLeviCoherenceStatement
import Langlands.BruhatTits.Iwasawa.PointProducts

/-! # Actual semistandard orbit packets from whole-domain continuations -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.Iwasawa

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open ActualConjugateLeviCoherence (LeviNormalization)

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback r.literalLeviHomeomorph π.obj

namespace OrbitPacketData

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (products : DynamicParabolicProducts K.toSubgroup)
  (normalization : LeviNormalization r.hom Aπ)

include products in
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
private theorem factorization_of_dynamicParabolicProducts
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : rationalPoints G) :
    ∃ x : DynamicOppositeStandardIntertwining.parabolic χ, ∃ k : K,
      g = (x : rationalPoints G) * (k : rationalPoints G) := by
  have hg : g ∈ (Set.univ : Set (rationalPoints G)) := Set.mem_univ g
  rw [(products χ).1] at hg
  obtain ⟨x, hx, k, hk, hmul⟩ := Set.mem_mul.mp hg
  exact ⟨⟨x, hx⟩, ⟨k, hk⟩, hmul.symm⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
/-- Whole-domain continuation and the displayed split-central inducing data
give the actual scalar package used by semistandard synthesis. -/
def conditionalOfFullDomainContinuation
    (continuation : ActualOppositeFullDomainContinuationStatement.{u, uV}) :
    OrbitPacketData r π := by
  let hPK := factorization_of_dynamicParabolicProducts K products r.hom
  let hOppK := factorization_of_dynamicParabolicProducts K products
    (Dynamic.inverseCocharacter r.hom)
  have hc := continuation r.hom hG K hK hPK hOppK Aπ normalization.irreducible
    normalization.center normalization.central normalization.quotientMeasure
    normalization.squareIntegrable
  let forward := Classical.choice hc.1.1
  let reverse := Classical.choice hc.2.1
  let DForward := Classical.choose hc.1.2
  let DReverse := Classical.choose hc.2.2
  have hf := Classical.choose_spec hc.1.2
  have hr := Classical.choose_spec hc.2.2
  let Z := Classical.choose normalization.splitCenter
  let a : Z.toGrp ⟶ parameterScheme r.hom :=
    Classical.choose (Classical.choose_spec normalization.splitCenter)
  have ha := Classical.choose_spec (Classical.choose_spec normalization.splitCenter)
  have hsplit : normalization.center =
      ((parameterHomeomorph r.hom).toMonoidHom.comp (rationalPoints.map a)).range := by
    rw [MonoidHom.range_comp]
    exact ha.2
  let density := DynamicInducedOrbit.DensityPackage.ofSquareIntegrable i r.cocharacter
    relativeRootReflectionExistence centralSplitTorusCharacter hG K hK hPK hOppK Aπ
    forward reverse (DForward := DForward) (DReverse := DReverse)
    hf.1 hf.2.1 hf.2.2 hr.1 hr.2.1 hr.2.2 a ha.1 normalization.center
    normalization.central normalization.quotientMeasure hsplit normalization.irreducible
    normalization.squareIntegrable
  exact
    { reflection := relativeRootReflectionExistence
      centralCharacters := centralSplitTorusCharacter
      compact := density.K
      isCompact := density.hK
      factorization := density.hPK
      oppositeFactorization := density.hOppK
      forward := density.p
      reverse := density.q
      forwardDomain := density.DForward
      forwardOpen := density.hDForward
      forwardNonempty := density.hneForward
      forwardContained := density.hDForwardΩ
      reverseDomain := density.DReverse
      reverseOpen := density.hDReverse
      reverseNonempty := density.hneReverse
      reverseContained := density.hDReverseΩ
      irreducibleDomain := density.D
      irreducibleOpen := density.hD
      irreducibleNonempty := density.hne
      irreducible := density.hirr
      inverseRegular := density.hreg }

set_option maxRecDepth 4096 in
/-- Both compact pictures in the packet use the specified subgroup. -/
@[simp] theorem conditionalOfFullDomainContinuation_compact
    (continuation : ActualOppositeFullDomainContinuationStatement.{u, uV}) :
    (conditionalOfFullDomainContinuation r π K hK products normalization continuation).compact = K :=
  rfl

end OrbitPacketData

end Langlands.HarishChandraSchwartz.RationalSemistandard
