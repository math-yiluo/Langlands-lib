import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakPacketLowerEstimates
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviDensityCompactChange
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDynamicIwasawa

/-! # The weak estimate for the original weight from the common compact -/

noncomputable section

set_option maxRecDepth 10000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance weakTermAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance weakTermLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance weakTermLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance weakTermLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "χ" => (CommGroupScheme.groupHom ζ ≫ i)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (P : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))

set_option hygiene false in
local notation "forwardFactors" =>
  factorization_subtype (isIwasawaPair_dynamicParabolic_of_minimal hG hi hν hPK χ)
set_option hygiene false in
local notation "reverseFactors" =>
  factorization_subtype (isIwasawaPair_dynamicParabolic_of_minimal hG hi hν hPK
    (Dynamic.inverseCocharacter χ))

/-- Use the packet compact for the upper continuation in the weighted
expansion, preserving the inducing representation and the character space. -/
def upperDensityAtPacketCompact :
    DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
      (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj) :=
  P.changeCompact K hKc forwardFactors reverseFactors

set_option hygiene false in
local notation "PG" => upperDensityAtPacketCompact hG hi hν I hζ hKc hPK π hRefl hCST P

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine Tc.X.left]
  (sc : Tc.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (hs : IsSplitComponent sc)
  (hindex : (RenardCartan.splitValuationImage sc).FiniteIndex)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [(rationalPoints.map sc).range.Normal]
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (I' : Finset (SimpleRoot i ν))
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ T.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
  (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PM : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (R.normalizer s) (R.levi_le s) π hRefl hCST)
  (hMK : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf
    (standardLeviPoints i ν (rootSet i ν I')))
    ((K : Subgroup (rationalPoints G)).subgroupOf (standardLeviPoints i ν (rootSet i ν I'))))
  {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))

set_option hygiene false in
local notation "omegaπ" => discreteSeriesClass CM hCM mu π hsq
set_option hygiene false in
local notation "finiteUpper" => finite_standardLeviDiscreteSeriesStabilizer I sc hs hindex mu omegaπ
set_option hygiene false in
local notation "rhoX" => standardLeviUnitaryUnramifiedCharacterHaar I sc hs hindex

set_option maxHeartbeats 3500000 in
/-- Apply the weighted identities at one common compact, sum the lower
packet estimates, then recover the originally normalized weak integral. -/
theorem rationalOrbitLevelWeakPacketRapid_of_commonCompact_lowerEstimates
    (hproper : ∃ α : SimpleRoot i ν, α ∉ I')
    (hspecial : IsSpecialVertexCompact ν hi K)
    (hlifts : LiftsInCompact I I' (K := K) R)
    (hlowerK : ∀ s, (PM s).K.toSubgroup = leviSchemeCompact K.toSubgroup i ν (rootSet i ν I'))
    (hexp : WeightedWeakExpansionStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hsq
      hRefl hCST PG hA R PM)
    (hpacket : WeightedPacketIdentityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs hindex π mu hsq
      hRefl hCST PG hA R PM)
    (hbasis : SimultaneousStandardBasisAt i ν (K : Subgroup (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ (K : Subgroup (rationalPoints G)))
    (hlower : LowerDynamicPacketChamberEstimates hG hi hν I I' hζ hKc
      sc hs hindex π mu hsq hRefl hCST R PM hMK ρ) :
    letI := finiteUpper
    RationalOrbitLevelWeakPacketRapid hG hi hν I hKc hPK π CM hCM mu hsq I' hA ρ rhoX
      (standardLeviDensityPackageWeight hG hi hν I π CM hCM mu hsq hζ hRefl hCST P) := by
  let := finiteUpper
  have hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM :=
    fun s => ⟨rfl, hlowerK s⟩
  have hXi := hasRationalLeviXiHalfModulusComparison_of_basis hG hi hν
    (rootSet_subset i ν I') K.isOpen hKc hPK hMK hKc hbasis hcover
  have hweak := rationalOrbitLevelWeakPacketRapid_of_lowerEstimates hG hi hν I I' hζ hζ' hKc hPK
    sc hs hindex π mu hsq hRefl hCST PG hA R PM hMK ρ hproper hspecial hlifts hN hexp hpacket hXi hlower
  exact rationalOrbitLevelWeakPacketRapid_of_densityCompactChange hG hi hν I π CM hCM mu hsq
    hKc hPK I' hA ρ rhoX hζ hRefl hCST P K hKc forwardFactors reverseFactors hweak

end Langlands.HarishChandraSchwartz.WeakExpansion
