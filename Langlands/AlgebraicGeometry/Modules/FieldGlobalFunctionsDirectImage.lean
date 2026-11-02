import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Affine sections of the actual structure-sheaf direct image over a field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped ChangeOfRings TensorProduct

namespace Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions

section AffineRestriction

variable {Y T : Scheme.{u}} (p : Y ⟶ T) {U : T.Opens} (hU : IsAffineOpen U)

/-- The structure map of the actual inverse-image open is the pullback on
sections followed by the canonical identification with its global sections. -/
lemma structureRingHom_affineRestrict :
    structureRingHom (affineRestrict p hU) = p.app U ≫ (p ⁻¹ᵁ U).topIso.inv := by
  rw [affineRestrict, IsAffineOpen.isoSpec_hom,
    ← Scheme.Opens.toSpecΓ_naturality]
  rw [structureRingHom_eq_comp (p.app U) _ _ rfl]
  simp only [structureRingHom, Scheme.Opens.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

/-- Sections of the actual structure-module pushforward on the open `U`. -/
abbrev directImageSections (U : T.Opens) : ModuleCat.{u} Γ(T, U) :=
  ((Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)).val.obj (op U)

/-- The sections over the inverse-image open agree, with the actual base
scalar action, with sections of the actual direct image on `U`. -/
def affineRestrictSectionsIso :
    (relativeGlobalSections (affineRestrict p hU)).obj
        (SheafOfModules.unit (p ⁻¹ᵁ U).toScheme.ringCatSheaf) ≅
      directImageSections p U := by
  refine ModuleCat.isoMk
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
      (p ⁻¹ᵁ U).topIso) ?_
  intro r
  ext x
  change Γ((p ⁻¹ᵁ U).toScheme, ⊤) at x
  symm
  change (p ⁻¹ᵁ U).topIso.hom
      ((structureRingHom (affineRestrict p hU)).hom r * x) =
    p.app U r * (p ⁻¹ᵁ U).topIso.hom x
  rw [map_mul]
  congr 1
  have he : structureRingHom (affineRestrict p hU) ≫
      (p ⁻¹ᵁ U).topIso.hom = p.app U := by
    rw [structureRingHom_affineRestrict, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun a : Γ(T, U) ⟶ Γ(Y, p ⁻¹ᵁ U) => a r) he

end AffineRestriction

section FieldBaseChange

variable {k : Type u} [Field k] {X Y T : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (t : T ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ X) (p : Y ⟶ T)
  (h : IsPullback g p f t) {U : T.Opens} (hU : IsAffineOpen U)

/-- The actual field map to the coordinate ring of an affine open of the
arbitrary base. -/
def affineOpenFieldMap : CommRingCat.of k ⟶ Γ(T, U) :=
  Spec.preimage (hU.fromSpec ≫ t)

omit [IsProper f] in
include h in
/-- An affine open of an arbitrary base gives an actual affine field
base-change square for its inverse image. -/
lemma isPullback_affineOpen :
    IsPullback ((p ⁻¹ᵁ U).ι ≫ g) (affineRestrict p hU) f
      (Spec.map (affineOpenFieldMap t hU)) := by
  simpa [affineOpenFieldMap] using (isPullback_affineRestrict p hU).paste_horiz h

/-- Canonical scalar base change computes sections of the actual
structure-sheaf direct image on each affine open of any base scheme. -/
def directImageAffineSectionsIso :
    (ModuleCat.extendScalars (affineOpenFieldMap t hU).hom).obj (sections f) ≅
      directImageSections p U :=
  baseChangeIso f (affineOpenFieldMap t hU) (affineRestrict p hU)
      ((p ⁻¹ᵁ U).ι ≫ g) (isPullback_affineOpen f t g p h hU) ≪≫
    affineRestrictSectionsIso p hU

/-- The affine-open comparison is the canonical affine base-change map
followed by the actual inverse-open/direct-image identification. -/
lemma directImageAffineSectionsIso_hom :
    (directImageAffineSectionsIso f t g p h hU).hom =
      (baseChangeIso f (affineOpenFieldMap t hU) (affineRestrict p hU)
        ((p ⁻¹ᵁ U).ι ≫ g) (isPullback_affineOpen f t g p h hU)).hom ≫
          (affineRestrictSectionsIso p hU).hom := rfl

include h hU in
/-- Sections of the actual structure-sheaf direct image on each affine
open of an arbitrary base are finite over that open's coordinate ring. -/
lemma finite_directImageAffineSections :
    Module.Finite Γ(T, U) (directImageSections p U) := by
  let : Algebra k Γ(T, U) := (affineOpenFieldMap t hU).hom.toAlgebra
  let : Module.Finite k (sections f) := finite f
  let : Module.Finite Γ(T, U)
      ((ModuleCat.extendScalars (affineOpenFieldMap t hU).hom).obj (sections f)) :=
    inferInstanceAs (Module.Finite Γ(T, U) (Γ(T, U) ⊗[k] sections f))
  exact Module.Finite.equiv (directImageAffineSectionsIso f t g p h hU).toLinearEquiv

include h in
/-- The actual structure-sheaf direct image has finite sections on all
affine opens, without any finiteness hypothesis on the base scheme. -/
lemma hasFiniteAffineSections_directImage :
    Langlands.AlgebraicGeometry.Modules.HasFiniteAffineSections
      ((Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf)) := by
  intro U
  exact finite_directImageAffineSections f t g p h U.2

end FieldBaseChange

end Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions
