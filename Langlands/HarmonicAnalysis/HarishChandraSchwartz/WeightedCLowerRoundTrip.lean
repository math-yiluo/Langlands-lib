import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCRoundTripVertices

/-! # The lower round trip through the negative auxiliary parabolic -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open UnramifiedOperatorFamily StandardIntertwining DynamicCommonLeviComposition
  DynamicCommonLeviCompact DynamicCommonLeviContinuation ActualCommonLeviTensor
  DynamicOppositeCanonicalScalar ActualCommonLeviV3 ActualCommonLeviCompactTensor
  DynamicCommonLeviPresentations

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance cLowRTAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance cLowRTLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance cLowRTLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance cLowRTLeviFiniteType (J : Set (characterLattice T)) :
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
  ActualCommonLeviV3.leviLocallyCompact ActualCommonLeviV3.leviMeasurable ActualCommonLeviV3.leviBorel

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance cLowRTPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

local notation "χG" => CommGroupScheme.groupHom ζ ≫ i
local notation "χ" => χG ≫ (G.innerIso (n : rationalPoints G)).hom
local notation "m" => (n : rationalPoints G)
local notation "L" => parameterScheme χ
local notation "M" => RationalPointFamily.levi i ν I
local notation "fM" => leviRationalPointHomeomorph i ν I
local notation "eG" => standardLeviDynamicHomeomorph hG hi hν I hζ
local notation "cg" => leviConjugation χG m
local notation "e₁" => standardLeviParameterIso hG hi hν I hζ
local notation "e₂" => parameterConjugationIso χG m
local notation "eL" => lowerParameterIso hG hi hν I I' hζ n hn
local notation "eI" => auxiliaryInnerParameterIso hG hi hν I I' hζ hζ' n hn
local notation "b" => lowerCocharacter i ν (rootSet i ν I') ζ n
local notation "j₀" => Standard.leviHom i ν (rootSet i ν I)
local notation "j₁" => Standard.leviHom i ν (rootSet i ν I')
local notation "e_s" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
local notation "eIpt" => auxiliaryInnerLeviEquiv hG hi hν I I' hζ hζ' n hn

local notation "f" => weightedCParameterIso hG hi hν I hζ n
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
local notation "Φ" => unramifiedCharactersHomeomorph fM ν₀
local notation "liftParam" => rationalUnramifiedCharacterRestrict (f).hom
local notation "τ" => rationalUnramifiedCharacterRestrict (eI).hom
local notation "δG" => rationalUnramifiedCharacterRestrict (e₂).hom
local notation "Z" => unramifiedCharacters (normCharacters χ)
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
local notation "GR" => unramifiedRegularFunctions (normCharacters χG)
local notation "LR" => unramifiedRegularFunctions (normCharacters b)
local notation "hp" => parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
local notation "Frac" => rationalUnramifiedFunctionField L hp hL
local notation "φ" => algebraMap R Frac
local notation "E" => rationalUnramifiedRegularFunctionsEquiv (e₂)
local notation "E'" => rationalUnramifiedFunctionFieldEquiv (parameterProjection_continuous χG)
  (parameterScheme_isConnectedReductive χG hG) hp hL (e₂)
local notation "tG" => lowerAmbient_isConnectedReductive hG hi hν I'

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u}) (hCST : CentralSplitTorusCharacterStatement.{u})
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))

local notation "A₀" => SmoothRep.pullback eG π.obj
local notation "A" => conjugateRepresentation χG m A₀
local notation "B" => (lowerRepresentation hG hi hν I I' hζ n hn π).obj

variable (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG A₀)
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

attribute [local instance]
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel

local notation "θ₀" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
local notation "eχ" => weightedC_conjugatedCocharacter_eq (i := i) (ζ := ζ) n
local notation "Vertex" => GalleryVertex χ


local notation "θ" => (⟨χ, rfl⟩ : Vertex)
local notation "x" => weightedCAuxiliaryVertex hG hi hν I I' hζ n hn ζ'
  (outerCentralizer_pos hG hi hν I' hζ')
local notation "y" => weightedCAuxiliaryVertex hG hi hν I I' hζ n hn (-ζ')
  (outerCentralizer_neg hG hi hν I' hζ')
local notation "ox" => GalleryVertex.opposite x
local notation "oθ" => GalleryVertex.opposite θ
local notation "V" => ({θ, oθ, x, ox, y} : Finset Vertex)

variable (iw : ∀ (v : Vertex) (g : rationalPoints G), ∃ p : parabolic v.val, ∃ k : K,
  g = (p : rationalPoints G) * (k : rationalPoints G))
  (p : CompactContinuationSystem χ hG A K hK iw)

local notation "J[" v "," w "," z "]" => compactContinuationValue χ hG A K hK iw p v w z
local notation "R[" v "," w "]" => (p v w).regularRegion
local notation "U[" v "," z "]" => UnramifiedLeviInduction
  (commonDecomposition χ (v : Vertex).val (v : Vertex).property) (radical_isClosed (v : Vertex).val)
  (leviNormCharacters χ) (parameterTransport χ z) A
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "gConst" => (RationalPlancherelDensity.plancherelDensityConstant i ζ PG.K PG.hK : ℂ)
local notation "lConst" => (RationalPlancherelDensity.plancherelDensityConstant
  (Standard.leviTorusHom i ν (rootSet i ν I')) (conjugatedCocharacter i ζ n) PM.K PM.hK : ℂ)

local notation "Gδ" => weightedCAmbientDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "Lδ" => weightedCLowerDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  {sc : Tc.toGrp ⟶ L} (hs : IsSplitComponent sc)
  (hIr : (A).IsIrreducible) (hAd : (A).IsAdmissible)

local notation "AllRegular" => fun w : Z => ∀ v ∈ V, ∀ v' ∈ V, w ∈ R[v,v']

local notation "χs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
  Standard.leviTorusHom i ν (rootSet i ν I')


include hN in
set_option maxHeartbeats 20000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The lower package scalar evaluates the round trip through the negative
auxiliary parabolic, up to the product of the two Haar scales, and gives the
lower density as a reciprocal fraction. -/
theorem exists_weightedC_lowerRoundTrip (hPM : PM.canonicalScalar ≠ 0) :
    ∃ (Mnum Mden c₁ : R) (t₁ : ℝ≥0), 0 < t₁ ∧ Mnum ≠ 0 ∧ Mden ≠ 0 ∧ c₁ ≠ 0 ∧
      (∀ w : Z, w ∈ R[y,ox] → w ∈ R[ox,y] → c₁.val w ≠ 0 → ∀ si : ℂ,
        (J[ox,y,w]).comp (J[y,ox,w]) = si • LinearMap.id →
          si = (t₁ : ℂ) * (Mnum.val w / Mden.val w)) ∧
      (∀ z : unramifiedCharacters ν₀, ∀ hz : (Φ) z ∈ D₀, Mnum.val ((liftParam) z) ≠ 0 →
        Lδ ⟨(Φ) z, hz⟩ =
          lConst * (Mden.val ((liftParam) z) / Mnum.val ((liftParam) z))) := by
  obtain ⟨aM, bM, hbM, _, hMFrac, hMspec⟩ := package_compact_spec PM
  obtain ⟨t₁, ht₁, hM⟩ := auxiliaryInner_compare
    hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM hN (iw y) (iw ox) A
    (weightedCTranslatedCoefficientEquiv hG hi hν I I' hζ hζ' n hn π) (p y ox) (p ox y)
  have haM : aM ≠ 0 := by
    intro h
    apply hPM
    rw [hMFrac, h, map_zero, zero_div]
  let Mnum : R := rationalUnramifiedRegularFunctionsMap (eI).hom aM
  let Mden : R := rationalUnramifiedRegularFunctionsMap (eI).hom bM
  let c₁ : R := rationalUnramifiedRegularFunctionsMap (eI).hom PM.p.denominator *
    rationalUnramifiedRegularFunctionsMap (eI).hom PM.q.denominator
  have hc₁ : c₁ ≠ 0 :=
    weightedC_regular_mul_ne_zero hG n
      (rationalUnramifiedRegularFunctionsMap_iso_ne_zero (eI) (PM.p.denominator_ne_zero (PM.hneForward.mono PM.hDForwardΩ)))
      (rationalUnramifiedRegularFunctionsMap_iso_ne_zero (eI) (PM.q.denominator_ne_zero (PM.hneReverse.mono PM.hDReverseΩ)))
  refine ⟨Mnum, Mden, c₁, t₁, ht₁, rationalUnramifiedRegularFunctionsMap_iso_ne_zero (eI) haM,
    rationalUnramifiedRegularFunctionsMap_iso_ne_zero (eI) hbM, hc₁, ?_, ?_⟩
  · intro w hyo hoy hw si hsi
    have hw' : PM.p.denominator.val ((τ) w) * PM.q.denominator.val ((τ) w) ≠ 0 := hw
    obtain ⟨hPMp, hPMq⟩ := mul_ne_zero_iff.mp hw'
    exact hM w ⟨hyo, hoy⟩ ⟨hPMp, hPMq⟩ si _ hsi (hMspec ⟨(τ) w, hPMp, hPMq⟩)
  · intro z hz hnum
    change rationalValueAt (packageDensity PM) hz.2.2.fst = _
    have eLow := weightedC_restrict_lowerDensity hG hi hν I I' hζ hζ' n hn z
    have hnumM : aM.val ((parameterTransport b).symm (lowerUnramifiedCharacterConjugation
        hG hi hν I I' hζ n hn ((Φ) z))) = Mnum.val ((liftParam) z) := congrArg aM.val eLow.symm
    have hdenM : bM.val ((parameterTransport b).symm (lowerUnramifiedCharacterConjugation
        hG hi hν I I' hζ n hn ((Φ) z))) = Mden.val ((liftParam) z) := congrArg bM.val eLow.symm
    have hρM := packageDensity_value_of_scalarFraction PM hz.2.2.fst hMFrac (hnumM.symm ▸ hnum)
    rw [hρM, hnumM, hdenM]

end Langlands.HarishChandraSchwartz.WeakExpansion
