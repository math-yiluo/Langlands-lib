import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeightedSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitDensityFromOppositeContinuations
import Langlands.Representation.Plancherel.DynamicContinuationOpenFullDomain
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Actual semistandard orbit packets from open full domains -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.Plancherel.DynamicOppositeCanonicalScalar

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

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
  rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {p : SemistandardSpectralIndex i} {hG : IsConnectedReductive G}
  (r : CocharacterPresentation hG p)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom r.cocharacter ≫ i


open DynamicOppositeStandardIntertwining DynamicCommonLeviContinuation

set_option hygiene false in
local notation "M" => DynamicOppositeStandardIntertwining.levi χ
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback r.literalLeviHomeomorph π.obj

variable
  (hPK : ∀ g : rationalPoints G,
    ∃ p : DynamicOppositeStandardIntertwining.parabolic χ, ∃ k : K,
      g = (p : rationalPoints G) * (k : rationalPoints G))
  (hOppK : ∀ g : rationalPoints G,
    ∃ p : oppositeParabolic χ, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (a : T.toGrp ⟶ parameterScheme χ)
  (ha : IsSplitComponent a) (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (mu : Measure (M ⧸ C)) [mu.IsHaarMeasure]
  (hCsplit : C = ((parameterHomeomorph χ).toMonoidHom.comp (rationalPoints.map a)).range)
  (hsq : IsSquareIntegrableModCentralSubgroup C hC (Aπ).representation mu)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Open and nonempty actual full convergence domains give the scalar data
for the ordinary semistandard packet at the specified source compact. -/
def OrbitPacketData.conditionalOfOpenFullDomains
    (hfOpen : IsOpen (forwardFullDomainRegion χ K hK Aπ))
    (hf : (forwardFullDomainRegion χ K hK Aπ).Nonempty)
    (hrOpen : IsOpen (reverseFullDomainRegion χ K hK Aπ))
    (hr : (reverseFullDomainRegion χ K hK Aπ).Nonempty) : OrbitPacketData r π := by
  let hR := relativeRootReflectionExistence.{u}
  let hS := centralSplitTorusCharacter.{u}
  have hirr : (Aπ).IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.obj.representation r.literalLeviHomeomorph).mpr
      π.property.1
  have hfin := SmoothRep.hasFiniteLength_of_isIrreducible hirr
  let forward := forwardContinuationOfOpenFullDomain hG χ a ha K hK Aπ hR hS hPK hOppK
    hsq.1 hfin hfOpen hf
  let reverse := reverseContinuationOfOpenFullDomain hG χ a ha K hK Aπ hR hS hPK hOppK
    hsq.1 hfin hrOpen hr
  let density := DynamicInducedOrbit.DensityPackage.ofSquareIntegrable i r.cocharacter hR hS hG
    K hK hPK hOppK Aπ forward reverse hfOpen hf Set.Subset.rfl hrOpen hr Set.Subset.rfl a ha
    C hC mu hCsplit hirr hsq
  exact
    { reflection := hR
      centralCharacters := hS
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

end Langlands.HarishChandraSchwartz.RationalSemistandard
