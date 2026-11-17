import Langlands.GroupScheme.IdentityCotangentSections
import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineSectionGenerators

/-! # Restriction compatibility of actual identity cotangent sections -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.IdentityCotangent

open Langlands.Scheme
open Langlands.Scheme.Modules
open IdentityJet
open CoordinateWeights

variable {S : Scheme.{u}} (G : GroupScheme S) [IsAffineHom G.X.hom]

attribute [local instance] sectionAlgebra augmentationAlgebra augmentationScalarTower

/-- The algebraic differential in the affine model is the actual sheaf
differential section. -/
theorem differentialSectionsEquiv_inv_D (U : S.affineOpens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    (differentialSectionsEquiv G U).symm
        (KaehlerDifferential.D Γ(S, U) Γ(G.X.left, G.X.hom ⁻¹ᵁ U) a) =
      (relativeDifferentialsDerivation G.X.hom).app (G.X.hom ⁻¹ᵁ U) a := by
  have h := relativeDifferentialsSectionsIso_inv_D G.X.hom U.2 (affineOpen G U).2 le_rfl a
  have hAlg : (G.X.hom.appLE U (G.X.hom ⁻¹ᵁ U) le_rfl).hom.toAlgebra =
      sectionAlgebra G U := by
    rw [projection_appLE_self]
  exact moduleIso_inv_D_of_algebra_eq
    (M := Γ(relativeDifferentials G.X.hom, G.X.hom ⁻¹ᵁ U)) _ _ hAlg
    (relativeDifferentialsSectionsIso G.X.hom U.2 (affineOpen G U).2 le_rfl) a _ h

/-- The identity differential, expressed using the canonical augmentation quotient. -/
def identityDifferential (hG : Smooth G.X.hom) (U : S.affineOpens) :
    Γ(G.X.left, G.X.hom ⁻¹ᵁ U) →ₗ[Γ(S, U)] Γ(G.cotangentAtIdentity, U) :=
  (sectionsEquiv G hG U).symm.toLinearMap.comp (AugmentedAlgebra.classMap (augmentation G U))

/-- The identity differential is the pullback of the actual relative derivation. -/
theorem identityDifferential_apply (hG : Smooth G.X.hom) (U : S.affineOpens)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    identityDifferential G hG U a =
      sectionPullbackLE G.identitySection (relativeDifferentials G.X.hom)
        (le_of_eq (identity_preimage G U).symm)
        ((relativeDifferentialsDerivation G.X.hom).app (G.X.hom ⁻¹ᵁ U) a) := by
  apply (sectionsEquiv G hG U).injective
  change (sectionsEquiv G hG U) ((sectionsEquiv G hG U).symm
      (AugmentedAlgebra.classMap (augmentation G U) a)) = _
  rw [LinearEquiv.apply_symm_apply, ← differentialSectionsEquiv_inv_D G U a]
  exact (sectionsEquiv_pullback_model_D G hG U a).symm

/-- Restriction of actual functions above an inclusion of affine base opens. -/
def functionRestriction {U V : S.affineOpens} (h : V.1 ≤ U.1) :
    Γ(G.X.left, G.X.hom ⁻¹ᵁ U) →+* Γ(G.X.left, G.X.hom ⁻¹ᵁ V) :=
  (G.X.left.presheaf.map
    (homOfLE (show G.X.hom ⁻¹ᵁ V ≤ G.X.hom ⁻¹ᵁ U from fun _ hx => h hx)).op).hom

/-- The actual identity differential commutes with restriction of base opens. -/
theorem identityDifferential_restrict (hG : Smooth G.X.hom)
    {U V : S.affineOpens} (h : V.1 ≤ U.1)
    (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    G.cotangentAtIdentity.presheaf.map (homOfLE h).op (identityDifferential G hG U a) =
      identityDifferential G hG V (functionRestriction G h a) := by
  rw [identityDifferential_apply, identityDifferential_apply]
  let hU := le_of_eq (identity_preimage G U).symm
  let hV := le_of_eq (identity_preimage G V).symm
  let j : G.X.hom ⁻¹ᵁ V ≤ G.X.hom ⁻¹ᵁ U := fun _ hx => h hx
  have hmap := map_sectionPullbackLE G.identitySection (relativeDifferentials G.X.hom)
    hU h ((relativeDifferentialsDerivation G.X.hom).app (G.X.hom ⁻¹ᵁ U) a)
  have hpull := sectionPullbackLE_restrict G.identitySection (relativeDifferentials G.X.hom)
    j hV ((relativeDifferentialsDerivation G.X.hom).app (G.X.hom ⁻¹ᵁ U) a)
  have hd := (relativeDifferentialsDerivation G.X.hom).app_restrict (homOfLE j) a
  exact hmap.trans (hpull.symm.trans
    (congrArg (sectionPullbackLE G.identitySection (relativeDifferentials G.X.hom) hV) hd.symm))

/-- The semilinear augmentation-cotangent restriction transported from the actual
cotangent sheaf restriction. -/
def restriction (hG : Smooth G.X.hom) {U V : S.affineOpens} (h : V.1 ≤ U.1) :
    (RingHom.ker (augmentation G U)).Cotangent →ₛₗ[(S.presheaf.map (homOfLE h).op).hom]
      (RingHom.ker (augmentation G V)).Cotangent where
  toFun x := sectionsEquiv G hG V
    (G.cotangentAtIdentity.presheaf.map (homOfLE h).op ((sectionsEquiv G hG U).symm x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by simp only [map_smul, AlgebraicGeometry.Scheme.Modules.map_smul]

/-- The actual affine cotangent comparisons commute with their intrinsic
augmentation-cotangent restriction maps. -/
theorem sectionsEquiv_restrict (hG : Smooth G.X.hom) {U V : S.affineOpens}
    (h : V.1 ≤ U.1) (x : Γ(G.cotangentAtIdentity, U)) :
    restriction G hG h (sectionsEquiv G hG U x) =
      sectionsEquiv G hG V (G.cotangentAtIdentity.presheaf.map (homOfLE h).op x) := by
  change sectionsEquiv G hG V
    (G.cotangentAtIdentity.presheaf.map (homOfLE h).op
      ((sectionsEquiv G hG U).symm (sectionsEquiv G hG U x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Restriction sends each augmentation class to the class of the restricted
actual function. This identifies the transported map intrinsically. -/
theorem restriction_classMap (hG : Smooth G.X.hom) {U V : S.affineOpens}
    (h : V.1 ≤ U.1) (a : Γ(G.X.left, G.X.hom ⁻¹ᵁ U)) :
    restriction G hG h (AugmentedAlgebra.classMap (augmentation G U) a) =
      AugmentedAlgebra.classMap (augmentation G V) (functionRestriction G h a) := by
  change sectionsEquiv G hG V
      (G.cotangentAtIdentity.presheaf.map (homOfLE h).op (identityDifferential G hG U a)) = _
  rw [identityDifferential_restrict]
  change (sectionsEquiv G hG V) ((sectionsEquiv G hG V).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The augmentation-class formula uniquely specifies the intrinsic semilinear
restriction on actual cotangents. -/
theorem restriction_unique (hG : Smooth G.X.hom) {U V : S.affineOpens}
    (h : V.1 ≤ U.1)
    (L : (RingHom.ker (augmentation G U)).Cotangent →ₛₗ[(S.presheaf.map (homOfLE h).op).hom]
      (RingHom.ker (augmentation G V)).Cotangent)
    (hL : ∀ a, L (AugmentedAlgebra.classMap (augmentation G U) a) =
      AugmentedAlgebra.classMap (augmentation G V) (functionRestriction G h a)) :
    L = restriction G hG h := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (RingHom.ker (augmentation G U)).toCotangent_surjective x
  have hclass := AugmentedAlgebra.classMap_ideal (augmentation G U) a
  exact (congrArg L hclass.symm).trans ((hL a).trans
    ((restriction_classMap G hG h a).symm.trans (congrArg (restriction G hG h) hclass)))

end Langlands.GroupScheme.IdentityCotangent
