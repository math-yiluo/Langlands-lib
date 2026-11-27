import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionCFamily
import Langlands.Representation.Plancherel.RationalOperatorPoleTransport

/-! # The character parameter of each auxiliary c-integral -/

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance factorParameterAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance factorParameterLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance factorParameterLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance factorParameterLeviFiniteType (J : Set (characterLattice T)) :
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
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

variable (α : cocharacterLattice T)
  (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐌" => RationalPointFamily.levi i ν I
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "ψα" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "θs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
set_option hygiene false in
local notation "eα" => conjugationEquiv (n : rationalPoints G)
  (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)

local instance factorParameterPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "Φ" => unramifiedCharactersHomeomorph (leviRationalPointHomeomorph i ν I) ν₀

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν hζ hn hα in
private theorem auxiliaryCentralizer_eq_conjugated :
    Dynamic.centralizer ψα = conjugatedLevi i ν (rootSet i ν I) n :=
  (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).trans
    (conjugatedCocharacter_dynamic i ν (rootSet i ν I) hG hi hν (rootSet_subset i ν I) ζ hζ n).2.1

/-- Conjugation by the inverse lift identifies the auxiliary parameter scheme and the original
standard Levi scheme, compatibly with their ambient maps. -/
def factorParameterIso : parameterScheme ψα ≅ M₀ :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap (Dynamic.Affine.isRepresentedBy_centralizerHom ψα)
    (Standard.isRepresentedBy_leviHom i ν _) (G.innerIso (n : rationalPoints G)).symm
    (auxiliaryCentralizer_eq_conjugated hG hi hν I I' hζ n hn α hα).symm

set_option hygiene false in
local notation "E" => factorParameterIso hG hi hν I I' hζ n hn α hα

include hG hi hν hζ hn hα in
/-- The scheme isomorphism acts on the literal Levi by the conjugation used in `conjugateRep`. -/
theorem factorParameterIso_points (y : rationalPoints (parameterScheme ψα)) :
    leviRationalPointHomeomorph i ν I (rationalPoints.map (E).hom y) =
      eα (parameterHomeomorph ψα y) := by
  apply Subtype.ext
  rw [leviRationalPointHomeomorph_apply_coe, conjugationEquiv_apply,
    rationalPoints.map_apply, parameterHomeomorph_apply_coe]
  have he := SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_points
    (Dynamic.Affine.isRepresentedBy_centralizerHom ψα) (Standard.isRepresentedBy_leviHom i ν _)
    (G.innerIso (n : rationalPoints G)).symm
    (auxiliaryCentralizer_eq_conjugated hG hi hν I I' hζ n hn α hα).symm y
  refine he.trans ?_
  rw [Iso.symm_hom, ← innerIso_inv_hom, comp_innerIso_hom, constantPoint_self, inv_inv]

include hG hi hν hζ hn hα in
/-- The character of the auxiliary Levi evaluates as the original character on the inverse
conjugate point. -/
theorem factorParameterTransport_apply (z : unramifiedCharacters ν₀)
    (m : DynamicOppositeStandardIntertwining.levi ψα) :
    (parameterTransport ψα (rationalUnramifiedCharacterTransport (E).symm z)).val m =
      (Φ z).val (eα m) := by
  obtain ⟨y, rfl⟩ := (parameterHomeomorph ψα).surjective m
  let eM := leviRationalPointHomeomorph i ν I
  let eP := parameterHomeomorph ψα
  let f := rationalPoints.map (E).hom
  change z.val (f (eP.symm (eP y))) = z.val (eM.symm (eα (eP y)))
  rw [eP.symm_apply_apply]
  have h := factorParameterIso_points hG hi hν I I' hζ n hn α hα y
  change eM (f y) = eα (eP y) at h
  rw [← h, eM.symm_apply_apply]

set_option hygiene false in
local notation "tw(" z ")" => (Φ z).val.toMonoidHom
set_option hygiene false in
local notation "tz(" z ")" => parameterTransport ψα (rationalUnramifiedCharacterTransport (E).symm z)
set_option hygiene false in
local notation "Az(" B "," z ")" => (B).twist (tw(z)) (unramifiedCharacter_isOpen_ker (leviRationalNormCharacters i ν I) (Φ z))
set_option hygiene false in
local notation "conjRep" => conjugateRep hG hi hν I I' hζ n hn α hα

/-- The two twisting paths to the auxiliary integral give equivalent representations via the
identity on the coefficient carrier. -/
def factorConjugateTwistEquiv (B : SmoothRep.{0, u, uV} ℂ 𝐌) (z : unramifiedCharacters ν₀) :
    (conjRep (Az(B, z))).representation.Equiv
      ((conjRep B).twist (tz(z)).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker (leviNormCharacters ψα) (tz(z)))).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ B) (fun m => by
    apply LinearMap.ext
    intro v
    change ((Φ z).val (eα m) : ℂ) • B.representation (eα m) v =
      ((tz(z)).val m : ℂ) • B.representation (eα m) v
    rw [factorParameterTransport_apply hG hi hν I I' hζ n hn α hα])

end Langlands.HarishChandraSchwartz.WeakExpansion
