import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionContinuity
import Langlands.Representation.Plancherel.DiscreteSeriesOrbitTransport

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

universe u uV

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance (J : Set (characterLattice T)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance (J : Set (characterLattice T)) : IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

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

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')
  {K : OpenSubgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {Tc : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine Tc.X.left]
  (sc : Tc.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (hs : IsSplitComponent sc)
  (hindex : (RenardCartan.splitValuationImage sc).FiniteIndex)

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [(rationalPoints.map sc).range.Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ T.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
  (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PM : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (R.normalizer s) (R.levi_le s) π hRefl hCST)

set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "𝒲" => WeylIndex i ν (rootSet i ν I) (rootSet i ν I')
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hL" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "χ_" s => lowerCocharacter i ν (rootSet i ν I') ζ (R.normalizer s)
set_option hygiene false in
local notation "nₛ" => R.normalizer
set_option hygiene false in
local notation "hnₛ" => R.levi_le
set_option hygiene false in
local notation "baseClass" => discreteSeriesClass CM hCM mu π hsq
set_option hygiene false in
local notation "sC" s => lowerCentral hG hi hν I I' hζ (nₛ s) (hnₛ s) CM
set_option hygiene false in
local notation "hsC" s => lowerCentral_le_center hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM
set_option hygiene false in
local notation "smu" s => lowerMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu
set_option hygiene false in
local notation "sπ" s => lowerRepresentation hG hi hν I I' hζ (nₛ s) (hnₛ s) π
set_option hygiene false in
local notation "sSquare" s =>
  lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
set_option hygiene false in
local notation "sBaseClass" s => discreteSeriesClass (sC s) (hsC s) (smu s) (sπ s) (sSquare s)
set_option hygiene false in
local notation "sK" s => lowerK hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s)
set_option hygiene false in
local notation "skCompact" s =>
  lowerK_isCompact hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s)
set_option hygiene false in
local notation "skIwasawa" s =>
  lowerPackage_iwasawa hG hi hν I I' hζ (nₛ s) (hnₛ s) hRefl hCST π (PM s)
set_option hygiene false in
local notation "sWeight" s =>
  lowerPlancherelWeight hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq hRefl hCST (PM s)

set_option hygiene false in
local notation "sCoefficient" s =>
  DynamicInducedOrbit.inducedOrbitCoefficientMap (H := 𝐋) hL (χ_ s)
    (skCompact s) (skIwasawa s) (sπ s) (sC s) (hsC s) (smu s) (sSquare s)
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit CM hCM mu νM baseClass
set_option hygiene false in
local notation "sOrbit" s =>
  discreteSeriesOrbit (sC s) (hsC s) (smu s) (leviNormCharacters (χ_ s)) (sBaseClass s)
set_option hygiene false in
local notation "eₛ" s => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ (nₛ s) (hnₛ s)
set_option hygiene false in
local notation "characterMap" s => lowerCharacterConjugation hG hi hν I I' hζ (nₛ s) (hnₛ s)
set_option hygiene false in
local notation "hCharacterMap" s =>
  lowerCharacterConjugation_apply hG hi hν I I' hζ (nₛ s) (hnₛ s)
set_option hygiene false in
local notation "hCenterMap" s => lowerCentral_map_symm hG hi hν I I' hζ (nₛ s) (hnₛ s) CM
set_option hygiene false in
local notation "hQuotientMap" s => lowerMeasure_map hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu
set_option hygiene false in
local notation "packetIntegrand[" s "," q "," m "]" =>
  (fun ω : sOrbit s => (sWeight s) ω * (sCoefficient s) q ω m)
set_option hygiene false in
local notation "lowerPacket[" s "," ρ "," q "," m "]" =>
  DynamicInducedOrbit.inducedOrbitWavePacket (H := 𝐋) hL (χ_ s) (K := sK s)
    (skCompact s) (skIwasawa s) (sπ s) (sC s) (hsC s) (smu s) (sSquare s)
    (lowerCharacterMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) ρ) (sWeight s) q m

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
private theorem continuous_lowerPacketIntegrand (s : 𝒲)
    (q : LowerSections hG hi hν I I' hζ π hRefl hCST R PM s)
    (m : RationalPoint F 𝐋.X) :
    Continuous packetIntegrand[s, q, m] := by
  apply Continuous.mul
  · exact @DynamicInducedOrbit.continuous_orbitPlancherelWeight _ _ _ _ _ _ _ _ _
      (Standard.leviTorusHom i ν (rootSet i ν I'))
      (conjugatedCocharacter i ζ (nₛ s)) hRefl hCST hL (sπ s) (sC s)
      (lowerCentral_normal hG hi hν I I' hζ (nₛ s) (hnₛ s) CM) (hsC s)
      (lowerQuotientMeasurableSpace hG hi hν I I' hζ (nₛ s) (hnₛ s) CM) (smu s)
      (lowerMeasure_isHaarMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu) (sSquare s) (PM s)
  · exact @DynamicInducedOrbit.continuous_inducedOrbitCoefficientMap F _ _ _ _ 𝐋 _ _ hL (χ_ s)
      (sK s) (skCompact s) (skIwasawa s) (sπ s) (sC s)
      (lowerCentral_normal hG hi hν I I' hζ (nₛ s) (hnₛ s) CM) (hsC s)
      (lowerQuotientMeasurableSpace hG hi hν I I' hζ (nₛ s) (hnₛ s) CM) (smu s)
      (lowerMeasure_isHaarMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) CM mu) (sSquare s) q m

set_option maxHeartbeats 2000000 in
private def lowerOrbitHomeomorph (s : 𝒲) : Oπ ≃ₜ sOrbit s :=
  discreteSeriesOrbitCharacterEquiv (eₛ s).symm
    νM (leviNormCharacters (χ_ s)) (characterMap s) (hCharacterMap s) CM hCM
    (sC s) (hsC s) (hCenterMap s) mu (smu s) (hQuotientMap s) baseClass

set_option hygiene false in
local notation "transport[" s "]" => lowerOrbitHomeomorph hG hi hν I I' hζ sc hs π mu hsq R s
set_option hygiene false in
local notation "orbitMap[" s "]" => lowerOrbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq

set_option maxHeartbeats 2000000 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
private theorem lowerOrbitMap_eq_homeomorph (s : 𝒲) :
    orbitMap[s] = (transport[s] : Oπ → sOrbit s) := by
  funext ω
  obtain ⟨z, rfl⟩ :=
    (isOpenQuotientMap_discreteSeriesOrbitMap CM hCM mu νM baseClass).surjective ω
  exact (lowerOrbitMap_orbitMap hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq z).trans
    (discreteSeriesOrbitCharacterEquiv_orbitMap (eₛ s).symm
      νM (leviNormCharacters (χ_ s)) (characterMap s) (hCharacterMap s) CM hCM
      (sC s) (hsC s) (hCenterMap s) mu (smu s) (hQuotientMap s) baseClass z).symm

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 2048 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
private theorem measurePreserving_lowerOrbitHomeomorph
    [Finite (discreteSeriesStabilizer CM hCM mu νM baseClass)]
    (ρ : Measure (unitaryUnramifiedCharacters νM)) (s : 𝒲) :
    MeasurePreserving transport[s] (discreteSeriesOrbitMeasure νM CM hCM mu baseClass ρ)
      (letI := finite_lowerStabilizer hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
       discreteSeriesOrbitMeasure (leviNormCharacters (χ_ s)) (sC s) (hsC s) (smu s)
         (sBaseClass s) (lowerCharacterMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) ρ)) := by
  refine ⟨transport[s].continuous.measurable, ?_⟩
  let : Finite (discreteSeriesStabilizer (sC s) (hsC s) (smu s) (leviNormCharacters (χ_ s))
      (DiscreteSeriesClass.pullback (eₛ s).symm CM hCM (sC s) (hsC s) (hCenterMap s)
        mu (smu s) (hQuotientMap s) baseClass)) :=
    finite_lowerStabilizer hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
  unfold lowerOrbitHomeomorph lowerCharacterMeasure
  exact map_discreteSeriesOrbitMeasure_characterEquiv
    (eₛ s).symm νM (leviNormCharacters (χ_ s)) (characterMap s) (hCharacterMap s) CM hCM
    (sC s) (hsC s) (hCenterMap s) mu (smu s) (hQuotientMap s) baseClass ρ

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 2048 in
omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] in
private theorem integral_lowerPacketPullback
    [Finite (discreteSeriesStabilizer CM hCM mu νM baseClass)]
    (ρ : Measure (unitaryUnramifiedCharacters νM)) (s : 𝒲)
    [Finite (discreteSeriesStabilizer (sC s) (hsC s) (smu s)
      (leviNormCharacters (χ_ s)) (sBaseClass s))]
    (q : LowerSections hG hi hν I I' hζ π hRefl hCST R PM s) (m : RationalPoint F 𝐋.X) :
    (∫ ω, packetIntegrand[s, q, m] (orbitMap[s] ω)
      ∂discreteSeriesOrbitMeasure νM CM hCM mu baseClass ρ) =
      lowerPacket[s, ρ, q, m] := by
  let dO := discreteSeriesOrbitMeasure νM CM hCM mu baseClass ρ
  let ρs := lowerCharacterMeasure hG hi hν I I' hζ (nₛ s) (hnₛ s) ρ
  let dOs := discreteSeriesOrbitMeasure (leviNormCharacters (χ_ s)) (sC s) (hsC s) (smu s)
    (sBaseClass s) ρs
  let f : (sOrbit s) → ℂ := packetIntegrand[s, q, m]
  change (∫ ω, f (orbitMap[s] ω) ∂dO) = ∫ ω, f ω ∂dOs
  have hMeasure := measurePreserving_lowerOrbitHomeomorph hG hi hν I I' hζ sc hs π mu hsq R ρ s
  have hEmbedding : MeasurableEmbedding transport[s] := transport[s].measurableEmbedding
  have hChange : (∫ ω, f (transport[s] ω) ∂dO) = ∫ ω, f ω ∂dOs := by
    with_reducible_and_instances exact hMeasure.integral_comp hEmbedding f
  let integralAlong (e : Oπ → sOrbit s) := ∫ ω, f (e ω) ∂dO
  have hMap := lowerOrbitMap_eq_homeomorph hG hi hν I I' hζ sc hs π mu hsq R s
  with_reducible exact (congrArg integralAlong hMap).trans hChange

private theorem integral_eq_sum_of_pointwise {α J : Type*} [MeasurableSpace α] [Fintype J]
    (measure : Measure α) (f : α → ℂ) (g : J → α → ℂ) (P : J → ℂ)
    (hPointwise : ∀ x, f x = ∑ j, g j x)
    (hIntegrable : ∀ j, Integrable (g j) measure)
    (hIntegral : ∀ j, (∫ x, g j x ∂measure) = P j) :
    (∫ x, f x ∂measure) = ∑ j, P j := calc
  _ = ∫ x, ∑ j, g j x ∂measure := integral_congr_ae (Filter.Eventually.of_forall hPointwise)
  _ = ∑ j, ∫ x, g j x ∂measure := integral_finsetSum _ (fun j _ => hIntegrable j)
  _ = _ := Finset.sum_congr rfl fun j _ => hIntegral j

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2048 in
/-- The exact pointwise expansion implies the exact source-normalized packet identity. -/
def WeightedPacketIdentityReductionStatement : Prop :=
  WeightedWeakExpansionStatement hG hi hν I I' hζ hζ' hK hPK
    sc hs π mu hsq hRefl hCST PG hA R PM →
  WeightedPacketIdentityStatement hG hi hν I I' hζ hζ' hK hPK
    sc hs hindex π mu hsq hRefl hCST PG hA R PM

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2048 in
/-- Integrating the pointwise expansion gives the packet identity with the
source-normalized orbit measure and its conjugates. -/
theorem weightedPacketIdentity_of_weightedWeakExpansion :
    WeightedPacketIdentityReductionStatement hG hi hν I I' hζ hζ' hK hPK
      sc hs hindex π mu hsq hRefl hCST PG hA R PM := by
  intro hExpansion
  classical
  let : Fintype 𝒲 := @Fintype.ofFinite _ (finite_weylIndex i ν (rootSet i ν I)
    (rootSet i ν I') hG hi)
  let := finite_standardLeviDiscreteSeriesStabilizer I sc hs hindex mu baseClass
  unfold WeightedPacketIdentityStatement
  intro hProper hSpecial hLifts hNormalization q
  obtain ⟨extension, sections, hSections, hPointwise⟩ :=
    hExpansion hProper hSpecial hLifts hNormalization q
  refine ⟨extension, sections, hSections, ?_⟩
  intro m
  let ρ := standardLeviUnitaryUnramifiedCharacterHaar I sc hs hindex
  let dO := discreteSeriesOrbitMeasure νM CM hCM mu baseClass ρ
  let f (ω : Oπ) :=
    standardLeviPlancherelWeight hG hi hν I hζ π CM hCM mu hsq hRefl hCST
      PG.K PG.hK PG.hPK PG.hOppK PG.p PG.q PG.hDForward PG.hneForward PG.hDForwardΩ PG.hDReverse
      PG.hneReverse PG.hDReverseΩ PG.hD PG.hne PG.hirr PG.hreg ω *
        rationalOrbitWeakConstantTerm hG hi hν I hK hPK π CM hCM mu hsq I' hA q ω
          (leviRationalPointHomeomorph i ν I' m)
  let integrand (s : 𝒲) (ω : Oπ) := packetIntegrand[s, sections s, m] (orbitMap[s] ω)
  let packets (s : 𝒲) : ℂ :=
    haveI := finite_lowerStabilizer hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
    lowerPacket[s, ρ, sections s, m]
  change (∫ ω, f ω ∂dO) = ∑ s, packets s
  have hEq (ω : Oπ) : f ω = ∑ s, integrand s ω := by
    with_reducible exact hPointwise ω m
  have hIntegrable (s : 𝒲) : Integrable (integrand s) dO := by
    let : CompactSpace (unitaryUnramifiedCharacters νM) :=
      (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
    let := compactSpace_discreteSeriesOrbit CM hCM mu νM baseClass
    let : IsFiniteMeasure dO := isFiniteMeasure_standardLeviOrbitMeasure I sc hs hindex mu baseClass
    have hContinuous : Continuous packetIntegrand[s, sections s, m] :=
      continuous_lowerPacketIntegrand hG hi hν I I' hζ sc hs π mu hsq hRefl hCST R PM s (sections s) m
    have hOrbit : Continuous orbitMap[s] :=
      continuous_lowerOrbitMap hG hi hν I I' hζ sc hs π mu hsq R s
    have hPullback : Continuous (integrand s) := hContinuous.comp hOrbit
    exact hPullback.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntegral (s : 𝒲) : (∫ ω, integrand s ω ∂dO) = packets s := by
    let := finite_lowerStabilizer hG hi hν I I' hζ (nₛ s) (hnₛ s) CM hCM mu π hsq
    with_reducible_and_instances exact
      integral_lowerPacketPullback hG hi hν I I' hζ sc hs π mu hsq hRefl hCST R PM ρ s (sections s) m
  exact integral_eq_sum_of_pointwise dO f integrand packets hEq hIntegrable hIntegral

end Langlands.HarishChandraSchwartz.WeakExpansion
