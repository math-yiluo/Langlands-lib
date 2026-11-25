/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-!
# Module sheaves and modules over the constant ring sheaf

Source: Stacks Project, Modules on Sites, Section 18.11, Lemma 18.11.1.
(blueprint: new-constant-ring-module-sheaf-equivalence)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

private abbrev scalarRing (r : ℕ) := ULift.{u + 1} (ZMod r)

private abbrev liftedRing (r : ℕ) := ULift.{u + 1, u} (ULift.{u} (ZMod r))

-- Transport scalars without changing the underlying abelian groups.
private def liftIso (r : ℕ) : scalarRing.{u} r ≃+* liftedRing.{u} r :=
  (ULift.ringEquiv : scalarRing.{u} r ≃+* ZMod r).trans
    ((ULift.ringEquiv : ULift.{u} (ZMod r) ≃+* ZMod r).symm.trans
      (ULift.ringEquiv : liftedRing.{u} r ≃+* ULift.{u} (ZMod r)).symm)

private abbrev constRing (X : Scheme.{u}) (r : ℕ) : X.Etaleᵒᵖ ⥤ RingCat.{u + 1} :=
  (Functor.const X.Etaleᵒᵖ).obj (RingCat.of (scalarRing.{u} r))

private noncomputable abbrev ringSheaf (X : Scheme.{u}) (r : ℕ) :=
  (constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
    (RingCat.of (liftedRing.{u} r))

private noncomputable def scalarUnit (X : Scheme.{u}) (r : ℕ) :
    constRing X r ⟶ (ringSheaf X r).obj :=
  (Functor.const X.Etaleᵒᵖ).map (RingCat.ofHom (liftIso.{u} r).toRingHom) ≫
    toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of (liftedRing.{u} r)))

-- Over a constant ring presheaf, semilinear restriction maps are linear.
private noncomputable def modulesToFunctor (X : Scheme.{u}) (r : ℕ) :
    PresheafOfModules.{u + 1} (constRing X r) ⥤
      (X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (scalarRing.{u} r)) where
  obj M :=
    { obj U := M.obj U
      map f := ModuleCat.ofHom
        { toFun := M.map f
          map_add' := map_add (M.map f).hom
          map_smul' := fun a x ↦ M.map_smul f a x }
      map_id U := by ext x; exact congrArg (fun f ↦ f x) (M.map_id U)
      map_comp f g := by ext x; exact M.map_comp_apply f g x }
  map f :=
    { app U := f.app U
      naturality U V g := by ext x; exact PresheafOfModules.naturality_apply f g x }

private noncomputable def functorToModules (X : Scheme.{u}) (r : ℕ)
    (M : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (scalarRing.{u} r)) :
    PresheafOfModules.{u + 1} (constRing X r) where
  obj U := M.obj U
  map f := ModuleCat.ofHom
    { toFun := M.map f
      map_add' := map_add (M.map f).hom
      map_smul' := fun a x ↦ (M.map f).hom.map_smul a x }
  map_id U := by ext x; exact congrArg (fun f ↦ f x) (M.map_id U)
  map_comp f g := by ext x; exact congrArg (fun f ↦ f x) (M.map_comp f g)

private instance (X : Scheme.{u}) (r : ℕ) : (modulesToFunctor X r).Full where
  map_surjective f := by
    refine ⟨{ app := fun U ↦ f.app U, naturality := ?_ }, ?_⟩
    · intro U V g
      ext x
      exact congrArg (fun f ↦ f x) (f.naturality g)
    · rfl

private instance (X : Scheme.{u}) (r : ℕ) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (scalarUnit X r) := by
  have : IsIso (RingCat.ofHom (liftIso.{u} r).toRingHom) :=
    (liftIso.{u} r).toRingCatIso.isIso_hom
  have : IsIso ((Functor.const X.Etaleᵒᵖ).map
      (RingCat.ofHom (liftIso.{u} r).toRingHom)) := inferInstance
  unfold scalarUnit
  infer_instance

private instance (X : Scheme.{u}) (r : ℕ) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (scalarUnit X r) := by
  have : IsIso (RingCat.ofHom (liftIso.{u} r).toRingHom) :=
    (liftIso.{u} r).toRingCatIso.isIso_hom
  have : IsIso ((Functor.const X.Etaleᵒᵖ).map
      (RingCat.ofHom (liftIso.{u} r).toRingHom)) := inferInstance
  unfold scalarUnit
  infer_instance

-- Restrict the sheaf action along the lifted constant-presheaf unit.
private noncomputable def restriction (X : Scheme.{u}) (r : ℕ) :
    SheafOfModules.{u + 1} (ringSheaf X r) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (scalarRing.{u} r)) where
  obj M :=
    ⟨(modulesToFunctor X r).obj
        ((PresheafOfModules.restrictScalars (scalarUnit X r)).obj M.val),
      Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} (scalarRing.{u} r)) AddCommGrpCat.{u + 1})
        M.isSheaf⟩
  map f :=
    { hom := (modulesToFunctor X r).map
        ((PresheafOfModules.restrictScalars (scalarUnit X r)).map f.val) }

private noncomputable def restrictionUnderlying (X : Scheme.{u}) (r : ℕ) :
    restriction X r ⋙ sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (scalarRing.{u} r)) AddCommGrpCat.{u + 1}) ≅
      SheafOfModules.toSheaf (ringSheaf X r) := Iso.refl _

private instance (X : Scheme.{u}) (r : ℕ) : (restriction X r).Faithful :=
  Functor.Faithful.of_comp_iso (restrictionUnderlying X r)

-- Mathlib proves full faithfulness of restriction along a locally bijective ring map.
private instance (X : Scheme.{u}) (r : ℕ) : (restriction X r).Full := by
  let F := (SheafOfModules.forget (ringSheaf X r) ⋙
    PresheafOfModules.restrictScalars (scalarUnit X r)) ⋙ modulesToFunctor X r
  have : F.Full := inferInstance
  exact Functor.Full.of_comp_faithful_iso
    (G := sheafToPresheaf X.smallEtaleTopology _) (H := F) (Iso.refl F)

-- Sheafifying a module whose abelian presheaf is already a sheaf gives a preimage.
private instance (X : Scheme.{u}) (r : ℕ) : (restriction X r).EssSurj where
  mem_essImage N := by
    let P := functorToModules X r N.obj
    let M := (PresheafOfModules.sheafification.{u + 1} (scalarUnit X r)).obj P
    let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} (scalarUnit X r)).unit.app P
    let f : N.obj ⟶ ((restriction X r).obj M).obj := (modulesToFunctor X r).map η
    have hP : Presheaf.IsSheaf X.smallEtaleTopology P.presheaf :=
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (scalarRing.{u} r)) AddCommGrpCat.{u + 1})).obj N).property
    have hη : IsIso (toSheafify X.smallEtaleTopology P.presheaf) :=
      isIso_toSheafify _ hP
    have : IsIso ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
        (forget₂ (ModuleCat.{u + 1} (scalarRing.{u} r)) AddCommGrpCat.{u + 1}) |>.map f) :=
      hη
    have : IsIso f := isIso_of_reflects_iso f
      ((Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
        (forget₂ (ModuleCat.{u + 1} (scalarRing.{u} r)) AddCommGrpCat.{u + 1}))
    exact ⟨M, ⟨ObjectProperty.isoMk _ (asIso f).symm⟩⟩

/-- The two encodings of sheaves of modules over ZMod r are equivalent, compatibly
with their underlying abelian sheaves.
Source: Stacks Project, Modules on Sites, Section 18.11, Lemma 18.11.1
(https://stacks.math.columbia.edu/tag/03CY), applied to the constant ring presheaf.
(blueprint: new-constant-ring-module-sheaf-equivalence)

Proof: First identify the single and double lifts of ZMod r by the ring isomorphism
sending a lifted element to its twice-lifted value. A module-valued sheaf has an
action of the constant ring presheaf on its underlying abelian sheaf. Extend this
action to the sheafification of that presheaf: locally represent a section of the
constant ring sheaf by constant scalars, act on the restrictions of the module
section, and glue. Independence of representatives, the module laws and linearity
of maps are local assertions and follow from the original action and sheaf
uniqueness. Conversely restrict an action along the sheafification unit and the
ring isomorphism. The two constructions retain the underlying abelian sheaf and
all underlying morphisms. Uniqueness of the extended action gives inverse natural
isomorphisms, hence an equivalence and the displayed natural isomorphism of
forgetful functors. This works for r = 0 and r = 1 as well as for the empty scheme;
no nonzero scalar or nonempty covering assumption is used. -/
theorem constantRing_moduleSheaf_equivalence (X : Scheme.{u}) (r : ℕ) :
    ∃ E : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) ≌
      SheafOfModules.{u + 1}
        ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1, u} (ULift.{u} (ZMod r))))),
      Nonempty
        (sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
              AddCommGrpCat.{u + 1}) ≅
          E.functor ⋙ SheafOfModules.toSheaf _) := by
  have : (restriction X r).IsEquivalence := {}
  let e := (restriction X r).asEquivalence
  let H := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (scalarRing.{u} r)) AddCommGrpCat.{u + 1})
  refine ⟨e.symm, ⟨?_⟩⟩
  exact H.leftUnitor.symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm H ≪≫
    Functor.associator e.inverse (restriction X r) H ≪≫
    Functor.isoWhiskerLeft e.inverse (restrictionUnderlying X r)

end AlgebraicGeometry.Etale
