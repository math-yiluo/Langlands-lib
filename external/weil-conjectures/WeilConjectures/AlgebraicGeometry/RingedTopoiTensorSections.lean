/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Section calculus for the ringed-topos tensor comparison

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL.
(auxiliary; not a blueprint node).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules.RingedTensor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/-- The underlying sheaf of rings of a commutative ring sheaf.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
abbrev ringSheaf {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- The functor forgetting a module sheaf to its sheaf of sets.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable abbrev underlying {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringSheaf R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

/-- Restriction of scalars along the given morphism of ring sheaves.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable abbrev restriction
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

/-- Sectionwise extension of scalars, with its action on module morphisms.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def tensorPresheafFunctor
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ PresheafOfModules.{u} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{u, u, u} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{u, u, u} c M ⟶
      changeOfRingsPresheaf.{u, u, u} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{u, u, u} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

/-- Extension of scalars followed by module sheafification.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def tensorFunctor
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ SheafOfModules.{u} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

/-- Evaluate a sectionwise scalar-extension map on tensors with first factor one.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def tensorToRestriction
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (f : changeOfRingsPresheaf.{u, u, u} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [SheafOfModules.tensorRestriction_tmul, map_one] at h
        exact h }

/-- Extend a restriction-of-scalars map by the sectionwise tensor universal property.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def restrictionToTensor
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{u, u, u} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{u, u, u} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [SheafOfModules.tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

/-- The sectionwise extension/restriction adjunction, compatible with restrictions.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def tensorPresheafHomEquiv
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    (changeOfRingsPresheaf.{u, u, u} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

/-- The scalar-extension Hom equivalence after module sheafification.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def tensorHomEquiv
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

/-- The adjunction between sheafified extension and restriction of scalars.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def tensorAdjunction
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply]
        have h := SheafOfModules.tensorHomEquiv_naturality_left c a H
          ((tensorHomEquiv c N H).symm g)
        change tensorHomEquiv c M H
          ((tensorFunctor c).map a ≫ (tensorHomEquiv c N H).symm g) =
          a ≫ tensorHomEquiv c N H ((tensorHomEquiv c N H).symm g) at h
        rw [Equiv.apply_symm_apply] at h
        exact h.symm
      homEquiv_naturality_right := by
        intro M H H' f b
        exact SheafOfModules.tensorHomEquiv_naturality_right c M f b }

/-- The underlying sheaf morphism of the scalar-extension adjunction unit.
Source: Stacks Project, Modules on Sites, Tag 03D7
(auxiliary; not a blueprint node). -/
noncomputable def tensorUnit
    {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A)) :
    (underlying A).obj M ⟶ (underlying S).obj ((tensorFunctor c).obj M) :=
  (underlying A).map ((tensorAdjunction c).unit.app M)

section Pure
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- The image of a sectionwise pure tensor in the sheaf tensor.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def pure (M N : SheafOfModules.{u} (ringSheaf R))
    (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n))

/-- Pure tensors commute with restriction. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
theorem pure_restrict (M N : SheafOfModules.{u} (ringSheaf R))
    {W V : Cᵒᵖ} (i : W ⟶ V) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.map i (pure R M N W m n) =
      pure R M N V (M.val.map i m) (N.val.map i n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  let v := m ⊗ₜ[R.obj.obj W] n
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val i ((adj.unit.app (M.val ⊗ N.val)).app W v)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i v
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)

/-- The canonical bilinear pairing, as a presheaf morphism.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def pureMap (M N : SheafOfModules.{u} (ringSheaf R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val

/-- The linear pairing on sections. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
noncomputable def pureBilin (M N : SheafOfModules.{u} (ringSheaf R)) (W : Cᵒᵖ) :
    M.val.obj W →ₗ[R.obj.obj W] N.val.obj W →ₗ[R.obj.obj W]
      ((monoidalCategory R).tensorObj M N).val.obj W :=
  TensorProduct.curry ((pureMap R M N).app W).hom

/-- A map from a tensor is determined by pure sections. Source: Stacks 03EK
(auxiliary; not a blueprint node).
Proof: use the module sheafification adjunction, then sectionwise tensor generation. -/
theorem pure_hom_ext (M N H : SheafOfModules.{u} (ringSheaf R))
    {f g : (monoidalCategory R).tensorObj M N ⟶ H}
    (h : ∀ W m n, f.val.app W (pure R M N W m n) =
      g.val.app W (pure R M N W m n)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h W m n

private lemma tensorIso_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification F' G').hom =
      (tensorObjIsoSheafification F G).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  erw [tensorHom_def, Category.assoc,
    whiskerLeft_tensorObjIsoSheafification_hom (R := R) F' g,
    ← Category.assoc,
    whiskerRight_tensorObjIsoSheafification_hom (R := R) f G,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf pairing into the sheaf tensor is natural in both modules.
Source: Stacks Project, Modules on Sites, Tag 03EK
(auxiliary; not a blueprint node). -/
theorem pureMap_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    pureMap R F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ pureMap R F' G' := by
  let := monoidalCategory R
  have h : (tensorObjIsoSheafification F G).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification F' G').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hval := congrArg Hom.val h
  change (tensorObjIsoSheafification F G).inv.val ≫ (f ⊗ₘ g).val =
    ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val ≫
      (tensorObjIsoSheafification F' G').inv.val at hval
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit
  have hn := η.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ η.app (F'.val ⊗ G'.val) =
    η.app (F.val ⊗ G.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val at hn
  unfold pureMap
  erw [Category.assoc, hval, ← Category.assoc, ← hn]
  rfl

/-- Tensor morphisms act componentwise on pure sections. Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
theorem pure_map {M M' N N' : SheafOfModules.{u} (ringSheaf R)}
    (f : M ⟶ M') (g : N ⟶ N') (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorHom f g).val.app W (pure R M N W m n) =
      pure R M' N' W (f.val.app W m) (g.val.app W n) := by
  exact congrArg (fun k ↦ k.app W (m ⊗ₜ[R.obj.obj W] n)) (pureMap_natural R f g)
end Pure

end SheafOfModules.RingedTensor
