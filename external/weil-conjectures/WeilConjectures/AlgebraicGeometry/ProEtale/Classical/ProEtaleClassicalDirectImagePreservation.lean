/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedEquivalence

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Classicality of bounded-below direct images

## References

* Stacks Tag 09A6
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
-- Restriction along constant scalar sections retains every underlying section.
private noncomputable def intrinsicRestriction (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} Λ)))) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) where
  obj F := ⟨moduleSectionPresheaf Λ F,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1}) F.isSheaf⟩
  map f := { hom :=
    { app := fun W ↦ (ModuleCat.restrictScalars
        ((Functor.whiskerRight
          (toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app W).hom).map (f.val.app W)
      naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x } }

private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).Additive where
  map_add := by intros; ext W x; rfl

private noncomputable def intrinsicPresheaf (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) ⥤
      PresheafOfModules.{u + 1}
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} Λ))) where
  obj F := { obj := F.obj
             map := F.map
             map_id W := by ext x; exact ConcreteCategory.congr_hom (F.map_id W) x
             map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map f := { app := f.app
             naturality g := by ext x; exact ConcreteCategory.congr_hom (f.naturality g) x }

-- Local surjectivity of constant sections makes scalar restriction fully faithful.
private noncomputable def intrinsicRestrictionFullyFaithful (X : Scheme.{u}) (Λ : Type u)
    [CommRing Λ] : (intrinsicRestriction X Λ).FullyFaithful := by
  let := (Scheme.proEtaleConstantRingUnit_locallyBijective X Λ).2
  exact {
    preimage {M N} f := ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) N.isSheaf).symm
        ((intrinsicPresheaf X Λ).map f.hom)⟩
    map_preimage := by intro M N f; ext W x; rfl
    preimage_map := by intro M N f; ext W x; rfl }

private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).Full := (intrinsicRestrictionFullyFaithful X Λ).full
private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).Faithful := (intrinsicRestrictionFullyFaithful X Λ).faithful

-- Sheafification supplies the inverse on objects; its unit is already an isomorphism.
private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).EssSurj where
  mem_essImage F := by
    let := (Scheme.proEtaleConstantRingUnit_locallyBijective X Λ).1
    let := (Scheme.proEtaleConstantRingUnit_locallyBijective X Λ).2
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing X Λ)
    let α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} Λ)) ⟶ R.obj :=
      Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let P := (intrinsicPresheaf X Λ).obj F.obj
    let M := (PresheafOfModules.sheafification.{u + 1} (R := R) α).obj P
    let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} (R := R) α).unit.app P
    let η' : F ⟶ (intrinsicRestriction X Λ).obj M :=
      { hom := { app := η.app
                 naturality := fun {_ _} f ↦ by
                   ext x
                   exact PresheafOfModules.naturality_apply η f x } }
    have hη : IsIso η := by
      apply (isIso_iff_of_reflects_iso η (PresheafOfModules.toPresheaf _)).mp
      change IsIso (toSheafify (Scheme.ProEt.topology X) P.presheaf)
      exact isIso_toSheafify _ ((sheafCompose _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1})).obj F).property
    have : IsIso η := hη
    have : IsIso η' := by
      apply (isIso_iff_of_reflects_iso η' (sheafToPresheaf _ _)).mp
      change IsIso η'.hom
      have (W : X.ProEtᵒᵖ) : IsIso (η'.hom.app W) := by
        apply (isIso_iff_of_reflects_iso _
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1})).mp
        change IsIso (((PresheafOfModules.toPresheaf _).map η).app W)
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    exact ⟨M, ⟨(asIso η').symm⟩⟩

private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).IsEquivalence := {}

private theorem coefficientUnit_comp {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] (W : Y.ProEtᵒᵖ) (a : ULift.{u + 1, u} Λ) :
    (Scheme.proEtaleCoefficientDirectImageMap g Λ).hom.app W
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))).app W a) =
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))).app
        ((Scheme.proEtaleBaseChange g).op.obj W) a := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))
    ((Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      (Scheme.proEtaleConstantRing X Λ))).apply_symm_apply
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange g).op
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))))
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h W) a

-- The section functions are identities; the coefficient-unit equation proves linearity.
private noncomputable def restrictionDirectImageIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] :
    Scheme.proEtaleConstantModuleDirectImage g Λ ⋙ intrinsicRestriction Y Λ ≅
      intrinsicRestriction X Λ ⋙ lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
    refine NatIso.ofComponents (fun W ↦ ?_) ?_
    · let L := ((intrinsicRestriction Y Λ).obj
          ((Scheme.proEtaleConstantModuleDirectImage g Λ).obj M)).obj.obj W
      let R := ((intrinsicRestriction X Λ).obj M).obj.obj
          ((Scheme.proEtaleBaseChange g).op.obj W)
      let h : L ⟶ R := ModuleCat.ofHom (X := L) (Y := R)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            change (Scheme.proEtaleCoefficientDirectImageMap g Λ).hom.app W
              ((toSheafify (Scheme.ProEt.topology Y)
                ((Functor.const Y.ProEtᵒᵖ).obj
                  (CommRingCat.of (ULift.{u + 1, u} Λ)))).app W a) •
                  (show M.val.obj ((Scheme.proEtaleBaseChange g).op.obj W) from x) = _
            rw [coefficientUnit_comp]
            rfl }
      let i : R ⟶ L := ModuleCat.ofHom (X := R) (Y := L)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            change _ = (Scheme.proEtaleCoefficientDirectImageMap g Λ).hom.app W
              ((toSheafify (Scheme.ProEt.topology Y)
                ((Functor.const Y.ProEtᵒᵖ).obj
                  (CommRingCat.of (ULift.{u + 1, u} Λ)))).app W a) •
                  (show M.val.obj ((Scheme.proEtaleBaseChange g).op.obj W) from x)
            rw [coefficientUnit_comp]
            rfl }
      exact { hom := h, inv := i
              hom_inv_id := by ext x; rfl
              inv_hom_id := by ext x; rfl }
    · intro U V f
      ext x
      rfl
  · intro M N f
    ext W x
    rfl


end AlgebraicGeometry.ProEtale
