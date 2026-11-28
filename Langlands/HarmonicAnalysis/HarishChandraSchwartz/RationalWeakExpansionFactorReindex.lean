import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionFactorParameters
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCTranslatedLevi
import Langlands.Representation.Plancherel.DynamicOppositePairScalar

/-! # Reindexing the auxiliary and ambient Levi data for the c-factors -/

noncomputable section

set_option quotPrecheck false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] targetsAmbientAffine targetsLeviAffineHom targetsLeviAffine
  targetsLeviFiniteType

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
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (α : cocharacterLattice T)
  (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))

local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)
local notation "χG" => CommGroupScheme.groupHom ζ ≫ i
local notation "χ" => χG ≫ (G.innerIso (n : rationalPoints G)).hom
local notation "ψα" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i
local notation "eα" => conjugationEquiv (n : rationalPoints G)
  (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν hζ hn hα in
/-- The auxiliary and conjugated ambient cocharacters have the same centralizer. -/
theorem weightedC_factorCentralizer :
    Dynamic.centralizer ψα = Dynamic.centralizer χ :=
  (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).trans
    (congrArg Dynamic.centralizer (weightedC_conjugatedCocharacter_eq (i := i) (ζ := ζ) n))

local notation "hξ" => weightedC_factorCentralizer hG hi hν I I' hζ n hn α hα
local notation "δ" => parameterChangeIso ψα χ (hξ).symm
local notation "leviId" => leviChange ψα χ (hξ).symm
local notation "σ" => weightedCParameterIso hG hi hν I hζ n
local notation "σaux" => factorParameterIso hG hi hν I I' hζ n hn α hα

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The two parameter identifications with the original Levi agree after
identifying the common centralizer schemes. -/
theorem weightedC_factorParameter_hom :
    (δ).hom ≫ (σ).hom = (σaux).hom := by
  apply (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I)).hom_ext
  rw [Category.assoc, weightedCParameterIso_hom_comp, ← Category.assoc,
    parameterChangeIso_hom_comp]
  have hcomap :
      conjugatedLevi i ν (rootSet i ν I) n = Dynamic.centralizer ψα :=
    ((centralizer_auxiliary hG hi hν I I' hζ n hn α hα).trans
      (conjugatedCocharacter_dynamic i ν (rootSet i ν I)
        hG hi hν (rootSet_subset i ν I) ζ hζ n).2.1).symm
  exact (SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_comp
    (Dynamic.Affine.isRepresentedBy_centralizerHom ψα)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
    (G.innerIso (n : rationalPoints G)).symm hcomap).symm

local instance : TopologicalSpace (rationalPoints M₀) := rationalPointTopology F (M₀).X

/-- Pulling the ambient parameter back to the auxiliary Levi gives the character
used in the c-factor. -/
theorem weightedC_factorParameter_restrict
    (z : unramifiedCharacters (fun a => (rationalNormCharacters M₀ a).toMul)) :
    rationalUnramifiedCharacterRestrict (δ).hom
        (rationalUnramifiedCharacterRestrict (σ).hom z) =
      rationalUnramifiedParameterHomeomorph (σaux).symm z := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  change z.val (rationalPoints.map (σ).hom (rationalPoints.map (δ).hom x)) =
    z.val (rationalPoints.map (σaux).hom x)
  apply congrArg z.val
  rw [← rationalPoints_map_comp_apply,
    weightedC_factorParameter_hom hG hi hν I I' hζ n hn α hα]

local notation "eG" => standardLeviDynamicHomeomorph hG hi hν I hζ
local notation "cg" => leviConjugation χG (n : rationalPoints G)

private theorem weightedC_factorLevi_apply (x : levi ψα) :
    eG ((cg).symm ((leviId) x)) = eα x := by
  apply Subtype.ext
  rw [standardLeviDynamicHomeomorph_apply_coe, conjugationEquiv_apply]
  have h := leviConjugation_apply_coe χG (n : rationalPoints G) ((cg).symm ((leviId) x))
  rw [ContinuousMulEquiv.apply_symm_apply, leviChange_apply_coe] at h
  conv_rhs => rw [h]
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]

/-- The translated ambient coefficient and the c-factor coefficient have
equivalent auxiliary Levi actions via the identity on the carrier. -/
def weightedC_factorCoefficientEquiv (B : SmoothRep.{0, u, uV} ℂ (RationalPointFamily.levi i ν I)) :
    (SmoothRep.pullback (leviId)
      (conjugateRepresentation χG (n : rationalPoints G) (SmoothRep.pullback eG B))).representation.Equiv
      (conjugateRep hG hi hν I I' hζ n hn α hα B).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ B) (fun x => by
    change B.representation (eG ((cg).symm ((leviId) x))) = B.representation (eα x)
    exact congrArg B.representation (weightedC_factorLevi_apply hG hi hν I I' hζ n hn α hα x))

end Langlands.HarishChandraSchwartz.WeakExpansion
