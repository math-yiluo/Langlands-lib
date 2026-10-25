import Langlands.Geometry.EtaleScalarExtension
import Langlands.Geometry.EtaleScalarCoherence
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Identity and composition for sheafified scalar extension
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable (φ : R →+* A) (ψ : A →+* B) (χ : B →+* C)
variable (X : Scheme.{u})

/-- Extension by the identity is canonically the identity on coefficient sheaves. -/
def sheafExtendScalarsIdIso :
    sheafExtendScalars (RingHom.id R) X ≅ 𝟭 (EtaleDerivedSections.ModuleSheaf X R) :=
  (conjugateIsoEquiv Adjunction.id
    (sheafExtendRestrictScalarsAdj (RingHom.id R) X)).symm
      (sheafRestrictScalarsIdIso X).symm

/-- Extension by a composite is canonically successive sheafified extension. -/
def sheafExtendScalarsCompIso :
    sheafExtendScalars (ψ.comp φ) X ≅
      sheafExtendScalars φ X ⋙ sheafExtendScalars ψ X :=
  (conjugateIsoEquiv
    ((sheafExtendRestrictScalarsAdj φ X).comp (sheafExtendRestrictScalarsAdj ψ X))
    (sheafExtendRestrictScalarsAdj (ψ.comp φ) X)).symm
      (sheafRestrictScalarsCompIso φ ψ X).symm

/-- The identity extension comparison is conjugate to inverse identity restriction. -/
@[simp] theorem conjugate_sheafExtendScalarsIdIso_hom :
    conjugateEquiv Adjunction.id (sheafExtendRestrictScalarsAdj (RingHom.id R) X)
      (sheafExtendScalarsIdIso X).hom = (sheafRestrictScalarsIdIso X).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The composite extension comparison is conjugate to inverse composite restriction. -/
@[simp] theorem conjugate_sheafExtendScalarsCompIso_hom :
    conjugateEquiv
      ((sheafExtendRestrictScalarsAdj φ X).comp (sheafExtendRestrictScalarsAdj ψ X))
      (sheafExtendRestrictScalarsAdj (ψ.comp φ) X)
      (sheafExtendScalarsCompIso φ ψ X).hom =
        (sheafRestrictScalarsCompIso φ ψ X).inv :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- The identity comparison carries the extension unit to inverse identity restriction. -/
theorem sheafExtensionUnit_id (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafExtensionUnit (RingHom.id R) X).app F ≫
        (sheafRestrictScalars (RingHom.id R) X).map
          ((sheafExtendScalarsIdIso X).hom.app F) =
      (sheafRestrictScalarsIdIso X).inv.app F := by
  simpa [sheafExtensionUnit] using (unit_conjugateEquiv Adjunction.id
    (sheafExtendRestrictScalarsAdj (RingHom.id R) X)
    (sheafExtendScalarsIdIso X).hom F).symm

/-- The composite comparison carries one extension unit to the two successive units. -/
theorem sheafExtensionUnit_comp (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafExtensionUnit (ψ.comp φ) X).app F ≫
        (sheafRestrictScalars (ψ.comp φ) X).map
          ((sheafExtendScalarsCompIso φ ψ X).hom.app F) =
      (sheafExtensionUnit φ X).app F ≫
        (sheafRestrictScalars φ X).map
          ((sheafExtensionUnit ψ X).app ((sheafExtendScalars φ X).obj F)) ≫
        (sheafRestrictScalarsCompIso φ ψ X).inv.app
          ((sheafExtendScalars ψ X).obj ((sheafExtendScalars φ X).obj F)) := by
  simpa [Adjunction.comp_unit_app, sheafExtensionUnit, Category.assoc] using
    (unit_conjugateEquiv
      ((sheafExtendRestrictScalarsAdj φ X).comp (sheafExtendRestrictScalarsAdj ψ X))
      (sheafExtendRestrictScalarsAdj (ψ.comp φ) X)
      (sheafExtendScalarsCompIso φ ψ X).hom F).symm

/-- Splitting off extension by the source identity and removing it is identity. -/
theorem sheafExtendScalarsCompIso_id_left :
    (sheafExtendScalarsCompIso (RingHom.id R) φ X).hom ≫
        Functor.whiskerRight (sheafExtendScalarsIdIso X).hom (sheafExtendScalars φ X) ≫
        (Functor.leftUnitor (sheafExtendScalars φ X)).hom =
      𝟙 (sheafExtendScalars φ X) := by
  apply (conjugateEquiv (sheafExtendRestrictScalarsAdj φ X)
    (sheafExtendRestrictScalarsAdj φ X)).injective
  rw [← conjugateEquiv_comp _
    ((sheafExtendRestrictScalarsAdj (RingHom.id R) X).comp
      (sheafExtendRestrictScalarsAdj φ X))]
  rw [← conjugateEquiv_comp _ (Adjunction.id.comp (sheafExtendRestrictScalarsAdj φ X))]
  rw [conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
    conjugate_sheafExtendScalarsIdIso_hom]
  change _ ≫ conjugateEquiv
      ((sheafExtendRestrictScalarsAdj (RingHom.id R) X).comp
        (sheafExtendRestrictScalarsAdj φ X))
      (sheafExtendRestrictScalarsAdj (φ.comp (RingHom.id R)) X)
      (sheafExtendScalarsCompIso (RingHom.id R) φ X).hom = _
  rw [conjugate_sheafExtendScalarsCompIso_hom, conjugateEquiv_id]
  ext F U x
  rfl

/-- Splitting off extension by the target identity and removing it is identity. -/
theorem sheafExtendScalarsCompIso_id_right :
    (sheafExtendScalarsCompIso φ (RingHom.id A) X).hom ≫
        Functor.whiskerLeft (sheafExtendScalars φ X) (sheafExtendScalarsIdIso X).hom ≫
        (Functor.rightUnitor (sheafExtendScalars φ X)).hom =
      𝟙 (sheafExtendScalars φ X) := by
  apply (conjugateEquiv (sheafExtendRestrictScalarsAdj φ X)
    (sheafExtendRestrictScalarsAdj φ X)).injective
  rw [← conjugateEquiv_comp _
    ((sheafExtendRestrictScalarsAdj φ X).comp
      (sheafExtendRestrictScalarsAdj (RingHom.id A) X))]
  rw [← conjugateEquiv_comp _ ((sheafExtendRestrictScalarsAdj φ X).comp Adjunction.id)]
  rw [conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
    conjugate_sheafExtendScalarsIdIso_hom]
  change _ ≫ conjugateEquiv
      ((sheafExtendRestrictScalarsAdj φ X).comp
        (sheafExtendRestrictScalarsAdj (RingHom.id A) X))
      (sheafExtendRestrictScalarsAdj ((RingHom.id A).comp φ) X)
      (sheafExtendScalarsCompIso φ (RingHom.id A) X).hom = _
  rw [conjugate_sheafExtendScalarsCompIso_hom, conjugateEquiv_id]
  ext F U x
  rfl

/-- The two ways to split three coefficient extensions agree after associating functors. -/
theorem sheafExtendScalarsCompIso_assoc :
    (sheafExtendScalarsCompIso (ψ.comp φ) χ X).hom ≫
        Functor.whiskerRight (sheafExtendScalarsCompIso φ ψ X).hom
          (sheafExtendScalars χ X) ≫
        (Functor.associator (sheafExtendScalars φ X)
          (sheafExtendScalars ψ X) (sheafExtendScalars χ X)).hom =
      (sheafExtendScalarsCompIso φ (χ.comp ψ) X).hom ≫
        Functor.whiskerLeft (sheafExtendScalars φ X)
          (sheafExtendScalarsCompIso ψ χ X).hom := by
  apply (conjugateEquiv
    ((sheafExtendRestrictScalarsAdj φ X).comp
      ((sheafExtendRestrictScalarsAdj ψ X).comp (sheafExtendRestrictScalarsAdj χ X)))
    (sheafExtendRestrictScalarsAdj (χ.comp (ψ.comp φ)) X)).injective
  rw [← conjugateEquiv_comp _
    ((sheafExtendRestrictScalarsAdj (ψ.comp φ) X).comp
      (sheafExtendRestrictScalarsAdj χ X))]
  rw [← conjugateEquiv_comp _
    (((sheafExtendRestrictScalarsAdj φ X).comp
      (sheafExtendRestrictScalarsAdj ψ X)).comp (sheafExtendRestrictScalarsAdj χ X))]
  rw [conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugate_sheafExtendScalarsCompIso_hom, conjugate_sheafExtendScalarsCompIso_hom]
  rw [← conjugateEquiv_comp _
    ((sheafExtendRestrictScalarsAdj φ X).comp
      (sheafExtendRestrictScalarsAdj (χ.comp ψ) X))]
  rw [conjugateEquiv_whiskerLeft, conjugate_sheafExtendScalarsCompIso_hom]
  have h := conjugate_sheafExtendScalarsCompIso_hom φ (χ.comp ψ) X
  simp only [RingHom.comp_assoc] at h
  rw [h]
  ext F U x
  rfl

end Langlands.Geometry.EtaleCohomologyAction
