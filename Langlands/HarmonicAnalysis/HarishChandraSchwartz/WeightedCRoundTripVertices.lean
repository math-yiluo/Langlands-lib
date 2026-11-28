import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCTranslatedLevi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCDensityArithmetic
import Langlands.Representation.Plancherel.ConjugatedOppositeCompactData
import Langlands.Representation.Plancherel.DynamicContinuedGalleryRoundTrip
import Langlands.Representation.Plancherel.DenseOpenUnitaryParameters

/-! # Auxiliary vertices for the weighted c-family round trips -/

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

local instance cScalarAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance cScalarLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance cScalarLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance cScalarLeviFiniteType (J : Set (characterLattice T)) :
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

section GenericTransport

variable {H₁ H₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H₁.X.left] [IsAffine H₂.X.left]

local instance roundTripTopology₁ : TopologicalSpace (rationalPoints H₁) :=
  rationalPointTopology F H₁.X
local instance roundTripTopology₂ : TopologicalSpace (rationalPoints H₂) :=
  rationalPointTopology F H₂.X

/-- Pullback of a nonzero regular function along an isomorphism of group
schemes is nonzero. -/
theorem rationalUnramifiedRegularFunctionsMap_iso_ne_zero (e : H₁ ≅ H₂)
    {c : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters H₁ ψ).toMul)} (h : c ≠ 0) :
    rationalUnramifiedRegularFunctionsMap e.hom c ≠ 0 := by
  rw [← rationalUnramifiedRegularFunctionsEquiv_apply]
  exact (map_ne_zero_iff _ (rationalUnramifiedRegularFunctionsEquiv e).injective).mpr h

end GenericTransport

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance cScalarPointTopology : TopologicalSpace (rationalPoints M₀) :=
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

/-- The transverse auxiliary parabolics of the actual c-map are vertices
with the translated common Levi. -/
def weightedCAuxiliaryVertex (α : cocharacterLattice T)
    (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I')) : Vertex :=
  ⟨CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i,
    (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).trans (congrArg Dynamic.centralizer eχ)⟩

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

local notation "Gδ" => fun z : ↥(D₀) => rationalValueAt (packageDensity PG) z.property.2.1
local notation "Lδ" => fun z : ↥(D₀) => rationalValueAt (packageDensity PM) z.property.2.2.fst

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  {sc : Tc.toGrp ⟶ L} (hs : IsSplitComponent sc)
  (hIr : (A).IsIrreducible) (hAd : (A).IsAdmissible)

local notation "AllRegular" => fun w : Z => ∀ v ∈ V, ∀ v' ∈ V, w ∈ R[v,v']

local notation "χs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
  Standard.leviTorusHom i ν (rootSet i ν I')


include hG in
/-- Products of nonzero regular functions on the translated parameter scheme are nonzero. -/
theorem weightedC_regular_mul_ne_zero {a c : R} (ha : a ≠ 0) (hc : c ≠ 0) : a * c ≠ 0 := by
  let _ : IsDomain R := rationalUnramifiedRegularFunctions_isDomain L hp hL
  exact mul_ne_zero ha hc

/-- The ambient Plancherel density at a point of the weighted c-family domain. -/
def weightedCAmbientDensityValue (z : ↥(D₀)) : ℂ :=
  rationalValueAt (packageDensity PG) z.property.2.1

/-- The lower Plancherel density at a point of the weighted c-family domain. -/
def weightedCLowerDensityValue (z : ↥(D₀)) : ℂ :=
  rationalValueAt (packageDensity PM) z.property.2.2.fst

end Langlands.HarishChandraSchwartz.WeakExpansion
