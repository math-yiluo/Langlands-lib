import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLowerPacketDensity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupQuotientHaar
import Langlands.Representation.Plancherel.ActualOppositeFullDomainContinuationStatement

/-! # Whole-domain continuations at the compact of a lower Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerContinuationLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance lowerContinuationLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "L'" => Standard.leviScheme i ν (rootSet i ν I')
set_option hygiene false in
local notation "χ'" => lowerCocharacter i ν (rootSet i ν I') ζ n

variable {A : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (ha : IsSplitComponent a)

set_option hygiene false in
local notation "C" => rationalLeviSplitCenter I a
set_option hygiene false in
local notation "C'" => lowerCentral hG hi hν I I' hζ n hn C
set_option hygiene false in
local notation "M" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}

variable [(C).Normal] [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (mu : Measure (M ⧸ C)) [mu.IsHaarMeasure]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
include ha in
private theorem lowerMeasure_isInvInvariant :
    (lowerMeasure hG hi hν I I' hζ n hn C mu).IsInvInvariant := by
  let b := lowerParameterSplitComponent hG hi hν I I' hζ n hn a
  have hb := isSplitComponent_lowerParameterSplitComponent hG hi hν I I' hζ n hn a ha
  let e := parameterHomeomorph χ'
  have hC : IsClosed (C' : Set (levi χ')) := by
    rw [lowerCentral_eq_lowerParameterSplitRange hG hi hν I I' hζ n hn a, MonoidHom.range_comp]
    exact e.toHomeomorph.isClosedMap _ (isClosed_range_splitComponent (parameterScheme χ') b hb)
  let : IsClosed (C' : Set (levi χ')) := hC
  let : LocallyCompactSpace (levi χ') :=
    (DynamicOppositeStandardIntertwining.levi_isClosed χ').locallyCompactSpace
  let : SecondCountableTopology (levi χ') := TopologicalSpace.Subtype.secondCountableTopology _
  let : MeasurableSpace (levi χ') := borel _
  let : BorelSpace (levi χ') := ⟨rfl⟩
  have hmod (x : levi χ') : Measure.modularCharacter x = 1 :=
    (modularCharacter_continuousMulEquiv e.symm x).symm.trans
      (rationalReductiveUnimodularity F (parameterScheme χ')
        (parameterScheme_isConnectedReductive χ' (lowerAmbient_isConnectedReductive hG hi hν I'))
        standardCocharacter (e.symm x))
  let qMeasure := lowerMeasure hG hi hν I I' hζ n hn C mu
  let : qMeasure.IsMulRightInvariant :=
    Haar.centralSubgroupQuotient_isMulRightInvariant C'
      (lowerCentral_le_center hG hi hν I I' hζ n hn C (rationalLeviSplitCenter_le_center I a ha))
      hC hmod qMeasure
  exact Langlands.isInvInvariant_of_isMulRightInvariant qMeasure

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))
  (hsq : IsSquareIntegrableModCentralSubgroup C (rationalLeviSplitCenter_le_center I a ha)
    π.obj.representation mu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hFactors : StandardLeviDynamicIwasawaAt i ν K.toSubgroup)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The whole-domain continuation target supplies the lower density at
the literal trace of the original compact on the output Levi. -/
def lowerDensityPackageOfContinuation
    (continuation : ActualOppositeFullDomainContinuationStatement.{u, uV}) :
    {P : LowerDensityPackage hG hi hν I I' hζ n hn π
        relativeRootReflectionExistence centralSplitTorusCharacter //
      P.K.toSubgroup = leviSchemeCompact K.toSubgroup i ν (rootSet i ν I')} := by
  let K' := LowerChamber.lowerCompact I' K.isOpen
  have hK' := isCompact_leviSchemeCompact (i := i) (ν := ν) (J := rootSet i ν I') hKc
  have hP' := factorization_subtype (P := parabolic χ') (K := K')
    (hFactors (rootSet i ν I') (rootSet_subset i ν I') χ')
  have hOpp' := factorization_subtype (P := oppositeParabolic χ') (K := K')
    (hFactors (rootSet i ν I') (rootSet_subset i ν I') (Dynamic.inverseCocharacter χ'))
  let π' := lowerRepresentation hG hi hν I I' hζ n hn π
  let qMeasure := lowerMeasure hG hi hν I I' hζ n hn C mu
  let : qMeasure.IsInvInvariant := lowerMeasure_isInvInvariant hG hi hν I I' hζ n hn a ha mu
  have hC' := lowerCentral_le_center hG hi hν I I' hζ n hn C
    (rationalLeviSplitCenter_le_center I a ha)
  have hsq' := lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C
    (rationalLeviSplitCenter_le_center I a ha) mu π hsq
  have hc :=
    continuation (G := L') χ' (lowerAmbient_isConnectedReductive hG hi hν I') K' hK' hP' hOpp'
      π'.obj π'.property.1 C' hC' qMeasure hsq'
  let forward := Classical.choice hc.1.1
  let reverse := Classical.choice hc.2.1
  have hf := Classical.choose_spec hc.1.2
  have hr := Classical.choose_spec hc.2.2
  exact ⟨lowerDensityFromOppositeContinuations hG hi hν I I' hζ n hn a ha π mu hsq
    relativeRootReflectionExistence centralSplitTorusCharacter hKc hFactors forward reverse
    hf.1 hf.2.1 hf.2.2 hr.1 hr.2.1 hr.2.2, rfl⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
