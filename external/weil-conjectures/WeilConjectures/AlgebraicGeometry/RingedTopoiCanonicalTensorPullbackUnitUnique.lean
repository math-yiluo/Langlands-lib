/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData

/-! # Uniqueness of the normalized tensor-pullback unit

Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
open scoped ChangeOfRings

set_option linter.unusedVariables false in
/--
The proof cancels the tensor comparison and uses the tensor universal property to identify maps.
Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).
Proof in words: cancel the tensor comparison and apply the tensor universal property. -/
theorem canonicalRingedTensorComparison_unit_unique
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∀ (j j' : L.obj (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ),
      (      ∀ M : SheafOfModules.{u}
          ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) ) → (      ∀ M : SheafOfModules.{u}
          ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j'.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) ) → j = j' := by
  let := monoidalCategory S
  intro j j' hj hj'
  have h := (hj (SheafOfModules.unit
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).trans
      (hj' (SheafOfModules.unit
        ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).symm
  rw [cancel_epi, cancel_mono] at h
  apply Iso.ext
  apply (tensor_left_iff j.hom j'.hom).mp
  change (𝟙 (SheafOfModules.unit
    ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ⊗ₘ j.hom) =
    (𝟙 (SheafOfModules.unit
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ⊗ₘ j'.hom)
  have h' := congrArg
    (fun f ↦ (j.inv ⊗ₘ 𝟙 _) ≫ f ≫ (j.hom ⊗ₘ 𝟙 _)) h
  simpa only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    j.inv_hom_id] using h'

end SheafOfModules
