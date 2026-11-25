/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension

/-! # The module-to-abelian-sections part of the standard comparison

Source: Stacks Project, Tags 015E and 03FD.
(blueprint: new-module-cohomology-standard-sections-factorization)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem evaluate_right_factor
    {A B C : AddCommGrpCat.{u}} (s : A ≅ B) (c : B ≅ C) (a : A ≅ C)
    (h : s ≪≫ c = a) (x : A) : s.hom x = c.inv (a.hom x) := by
  subst a
  simp only [Iso.trans_hom, AddCommGrpCat.comp_apply, Iso.hom_inv_id_apply]

/-- The common-resolution module comparison at x equals the inverse acyclic-resolution
comparison applied to the exact-forgetting module resolution comparison at x.
Source: Stacks Project, Tags 015E and 03FD, first half of the standard-resolution
calculation in `new-module-cohomology-ext-standard-resolution-formula`.
(blueprint: new-module-cohomology-standard-sections-factorization)

Proof: Substitute the equality identifying I with the standard injective resolution
and the defining equation of a. The component of resolutionSectionsNatIso is,
by construction, resolutionForgetObjIso followed by sectionHomologyIso and the
inverse acyclic-resolution comparison. sectionHomologyIso is the identity because
both functor composites produce the same abelian section complex. Compose with
the forward acyclic-resolution comparison and cancel its inverse. The remaining
isomorphism is exactly a. Apply the inverse acyclic-resolution map to this
equality at x and cancel its hom followed by inv. Proof irrelevance identifies
the supplied QuasiIso proof
with the one used in the construction. This applies in every degree, including
zero, and to zero coefficients and empty schemes. -/
theorem standard_sections_factorization
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : InjectiveResolution F) (hI : I = injectiveResolution F)
    (hι : QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)) (.up ℕ) 0).inv.app F ≫
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex
          (.up ℕ)).map I.ι)) (p : ℕ)
    (a : (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F) ≅
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology p)
    (ha : a = (forget₂ _ AddCommGrpCat.{u}).mapIso
      (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) p) ≪≫
        (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso
          (forget₂ _ AddCommGrpCat.{u})).symm)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    (let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
      let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
      let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
      let V := forget₂ (ModuleCat.{u}
        ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
      ((resolutionSectionsNatIso G V T Γ p (sectionHomologyIso X p)
        (fun M _ ↦ forgottenInjectiveAcyclic X M)).app F).hom x) =
    (let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
      let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
      let ι := (HomologicalComplex.singleMapHomologicalComplex T (.up ℕ) 0).inv.app F ≫
        (T.mapHomologicalComplex (.up ℕ)).map I.ι
      letI : QuasiIso ι := hι
      (Γ.rightDerivedObjIsoOfResolution ι
        (fun n ↦ forgottenInjectiveAcyclic X (I.cocomplex.X n)) p).inv (a.hom x)) := by
  apply evaluate_right_factor _ _ a ?_ x
  subst I
  subst a
  dsimp only [resolutionSectionsNatIso, resolutionSectionsObjIso,
    sectionHomologyIso, resolutionForgetObjIso]
  rw [NatIso.ofComponents.app]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, Category.assoc,
    Iso.inv_hom_id]
  rfl


end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
