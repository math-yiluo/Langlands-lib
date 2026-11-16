import Langlands.Representation.Plancherel.StandardLeviPlancherelWeight
import Langlands.Representation.Plancherel.StandardLeviCharacterMeasure

/-! # Actual Plancherel wave packets for standard Levi subgroups -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General
open Langlands.Plancherel.UnramifiedOperatorFamily
open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open Langlands.Plancherel.DynamicOppositeCanonicalScalar
open Langlands.Plancherel.RationalDynamicSource Langlands.Plancherel.RationalPlancherelDensity

namespace Langlands.HarishChandraSchwartz

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
include hG hi hν hζ in
/-- The dynamic parabolic defining the scalar is the actual standard parabolic used by
the packet; this follows from the published standard-cocharacter theorem. -/
theorem standardLeviPlancherelParabolic_eq :
    parabolic χ = standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I) :=
  (congrArg (fun P : SubgroupFunctor G => P.carrier (Over.mk (𝟙 _)))
    ((standardCocharacter F G hG S i hi ν hν _ hζ.1).2 ζ hζ).1).symm

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu νM (discreteSeriesClass C hC mu π hsq)

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (Ks : OpenSubgroup (RationalPoint F G.X))
  (hKs : IsCompact (Ks : Set (RationalPoint F G.X)))
  (hPKs : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : Ks, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppKs : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : Ks,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
  (qrev : ReverseContinuation χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ Ks hKs Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ Ks hKs Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG Ks hKs hPKs hOppKs Aπ
  p qrev hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

variable (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  [Finite (discreteSeriesStabilizer C hC mu νM (discreteSeriesClass C hC mu π hsq))]
  (rhoX : Measure (unitaryUnramifiedCharacters νM))

set_option hygiene false in
local notation "W" => standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST
  Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
  hD hne hirr hreg

/-- Waldspurger's actual mu-weighted orbit integral, with the imported conditional weight. -/
def standardLeviPlancherelWavePacket
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G) : ℂ :=
  rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq rhoX W q g

/-- The wrapper is exactly the existing orbit integral with the actual Plancherel density. -/
theorem standardLeviPlancherelWavePacket_apply
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (g : rationalPoints G) :
    standardLeviPlancherelWavePacket hG hi hν I hζ π C hC mu hsq hRefl hCST
        Ks hKs hPKs hOppKs p qrev hDForward hneForward hDForwardΩ hDReverse hneReverse
        hDReverseΩ hD hne hirr hreg hKc hPK rhoX q g =
      ∫ omega : Oπ, W omega *
        rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq q omega g
        ∂discreteSeriesOrbitMeasure νM C hC mu (discreteSeriesClass C hC mu π hsq) rhoX :=
  rfl

end Langlands.HarishChandraSchwartz
