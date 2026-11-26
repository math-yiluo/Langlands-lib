import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLowerPacketOpenFullDomains
import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryContinuation

/-! # Actual lower packet density existence at the inherited compact -/

noncomputable section

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

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
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
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

local instance lowerDensityExistenceLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerDensityExistenceLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance lowerDensityExistenceLeviFiniteType (J : Set (characterLattice T)) :
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
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "χ'" => lowerCocharacter i ν (rootSet i ν I') ζ n

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "K'" => LowerChamber.lowerCompact I' K.isOpen
set_option hygiene false in
local notation "hK'" => isCompact_leviSchemeCompact (i := i) (ν := ν) (J := rootSet i ν I') hKc
set_option hygiene false in
local notation "π'" => lowerRepresentation hG hi hν I I' hζ n hn π
set_option hygiene false in
local notation "Ωf" => forwardFullDomainRegion χ' K' hK' (π').obj
set_option hygiene false in
local notation "Ωr" => reverseFullDomainRegion χ' K' hK' (π').obj

open DynamicCommonLeviComposition DynamicCommonLeviContinuation ActualCommonLeviV3

attribute [local instance] ActualCommonLeviV3.leviMeasurable
  ActualCommonLeviV3.leviBorel ActualCommonLeviV3.leviLocallyCompact

variable {A : CommGroupScheme (Spec (CommRingCat.of F))}
  (a : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (ha : IsSplitComponent a)

set_option hygiene false in
local notation "C" => rationalLeviSplitCenter I a
set_option hygiene false in
local notation "hC" => rationalLeviSplitCenter_le_center I a ha

variable [(C).Normal] [MeasurableSpace (𝐌 ⧸ C)] [hBorel : BorelSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

/-- Existence of the density data, including the actual opposite continuations,
for the conjugated inducing representation at the literal lower compact. -/
def LowerPacketDensityAtCompactStatement : Prop :=
  ∀ [BorelSpace (𝐌 ⧸ C)],
    IsCompact (K : Set (rationalPoints G)) →
      IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu →
      StandardLeviDynamicIwasawaAt i ν K.toSubgroup →
      ∃ P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST,
        P.K.toSubgroup = leviSchemeCompact K.toSubgroup i ν (rootSet i ν I')

include hsq hBorel in
set_option synthInstance.maxHeartbeats 150000 in
set_option maxHeartbeats 2400000 in
/-- The published IV.1.1 continuation with bounded smooth coefficients gives
an open subset of full convergence in each actual lower domain. -/
theorem lowerPacketFullDomains_nonemptyInterior
    (hFactors : StandardLeviDynamicIwasawaAt i ν K.toSubgroup) :
    (interior Ωf).Nonempty ∧ (interior Ωr).Nonempty := by
  let C' := lowerCentral hG hi hν I I' hζ n hn C
  let hC' := lowerCentral_le_center hG hi hν I I' hζ n hn C hC
  let : C'.Normal := lowerCentral_normal hG hi hν I I' hζ n hn C
  let : MeasurableSpace (levi χ' ⧸ C') := lowerQuotientMeasurableSpace hG hi hν I I' hζ n hn C
  let : BorelSpace (levi χ' ⧸ C') := lowerQuotientBorelSpace hG hi hν I I' hζ n hn C
  let mu' : Measure (levi χ' ⧸ C') := lowerMeasure hG hi hν I I' hζ n hn C mu
  let : mu'.IsHaarMeasure := lowerMeasure_isHaarMeasure hG hi hν I I' hζ n hn C mu
  have hG' := lowerAmbient_isConnectedReductive hG hi hν I'
  let hcof := compactOpenCofinal_of_nonarchimedean (levi χ')
  let : SecondCountableTopology (levi χ') :=
    TopologicalSpace.Subtype.secondCountableTopology (levi χ' : Set (rationalPoints L'))
  let : T2Space (rationalPoints L') := rationalPoint_t2Space F L'
  let : T2Space (levi χ') :=
    inferInstanceAs (T2Space {g : rationalPoints L' // g ∈ DynamicOppositeStandardIntertwining.levi χ'})
  let : LocallyCompactSpace (levi χ') :=
    (DynamicOppositeStandardIntertwining.levi_isClosed χ').locallyCompactSpace
  let : MeasurableSpace (levi χ' ⧸ Subgroup.center (levi χ')) := borel _
  let : BorelSpace (levi χ' ⧸ Subgroup.center (levi χ')) := ⟨rfl⟩
  have hunit : IsUnitarizable (π').obj.representation :=
    ⟨squareIntegrableCentralSubgroupForm C' hC' hcof
      (DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ' hG')
      (π').property.1 mu' (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn
        C hC mu π hsq)⟩
  have hfin := SmoothRep.hasFiniteLength_of_isIrreducible (π').property.1
  have hP' (g : rationalPoints L') :
      ∃ p : parabolic χ', ∃ k : K', g = (p : rationalPoints L') * (k : rationalPoints L') :=
    factorization_subtype (P := parabolic χ') (K := K')
      (hFactors (rootSet i ν I') (rootSet_subset i ν I') χ') g
  have hOpp' (g : rationalPoints L') :
      ∃ p : oppositeParabolic χ', ∃ k : K', g = (p : rationalPoints L') * (k : rationalPoints L') :=
    factorization_subtype (P := oppositeParabolic χ') (K := K')
      (hFactors (rootSet i ν I') (rootSet_subset i ν I') (Dynamic.inverseCocharacter χ')) g
  obtain ⟨_, Uf, hopenf, hnef, hsubf, _, _⟩ := commonLeviContinuationExists_of_unitarizable
    χ' hG' K' hK' χ' rfl hP' (Dynamic.inverseCocharacter χ')
    (Dynamic.centralizer_inverseCocharacter χ') hOpp' (π').obj (π').property.2 hfin hunit
  obtain ⟨_, Ur, hopenr, hner, hsubr, _, _⟩ := commonLeviContinuationExists_of_unitarizable
    χ' hG' K' hK' (Dynamic.inverseCocharacter χ') (Dynamic.centralizer_inverseCocharacter χ')
    hOpp' χ' rfl hP' (π').obj (π').property.2 hfin hunit
  exact ⟨hnef.mono (interior_maximal hsubf hopenf), hner.mono (interior_maximal hsubr hopenr)⟩

omit hBorel in
set_option maxHeartbeats 2000000 in
/-- If both entire domains are open, the literal lower density package exists. -/
theorem lowerPacketDensityAtCompact_of_isOpen_fullDomains
    (hForward : IsOpen Ωf) (hReverse : IsOpen Ωr) :
    LowerPacketDensityAtCompactStatement hG hi hν I I' hζ n hn π
      (K := K) (a := a) (ha := ha) (mu := mu) hRefl hCST := by
  intro _ _ hsq hFactors
  obtain ⟨hf, hr⟩ := lowerPacketFullDomains_nonemptyInterior
    hG hi hν I I' hζ n hn π hKc (a := a) (ha := ha) (mu := mu) (hsq := hsq) hFactors
  exact exists_lowerDensityPackage_at_compact_of_openFullDomains hG hi hν I I' hζ n hn π hKc
    a ha mu hsq hRefl hCST hFactors
    ⟨hForward, hf.mono interior_subset, hReverse, hr.mono interior_subset⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
