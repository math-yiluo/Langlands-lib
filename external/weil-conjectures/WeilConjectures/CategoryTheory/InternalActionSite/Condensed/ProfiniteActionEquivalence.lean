/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionSite

/-!
# Internal condensed actions as equivariant sheaves on the small profinite site

Source: paragraph (3) of the direct-image stability proof, action-site presentation
(blueprint: def-sfb-condensed-derived-invariants).

An internal action of a topological group `G` on an internal module over a condensed ring
`A` is the same as an equivariant sheaf of modules, for the group sheaf `S ↦ C(S, G)`, over
the section ring sheaf on the small model of `Profinite`. The functor `toSite` keeps the
section modules, restrictions, actions and linear maps definitionally.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar.ActionSite

variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The coefficient ring sheaf on the small model, as a sheaf of rings. -/
noncomputable abbrev siteRing : Sheaf modelPrecoverage.{u}.toGrothendieck RingCat.{u + 1} :=
  InternalActionSite.baseRing modelPrecoverage.toGrothendieck (ringSheaf A)

/-- Equivariant sheaves of modules on the small model for the group sheaf `C(-, G)`. -/
noncomputable abbrev SiteEquivariant :=
  InternalActionSite.EquivariantSheaf (K := groupPresheaf G) modelPrecoverage.toGrothendieck
    (siteRing A)

variable {A G}

/-- An internal action, read on the small model. -/
noncomputable def toSiteObj (M : Equivariant A G) : SiteEquivariant A G where
  obj :=
    { val := (PresheafOfModules.pushforward₀ (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _).obj
        ((sectionsFunctor A).obj M.module).val
      action :=
        { act X := (M.act ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)).comp
            (groupPresheafObjEquiv G X).toMonoidHom
          naturality f a m :=
            M.naturality _ _ ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop) a.down m } }
  property := Functor.op_comp_isSheaf (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _
    (coherentTopology Profinite.{u}) M.module.X

/-- The equivariant linear map read on the small model. -/
noncomputable def toSiteMap {M N : Equivariant A G} (f : M ⟶ N) : toSiteObj M ⟶ toSiteObj N :=
  ObjectProperty.homMk (X := toSiteObj M) (Y := toSiteObj N)
    ⟨(PresheafOfModules.pushforward₀ (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _).map
      ((sectionsFunctor A).map f.val).val, fun _ a m ↦ f.property _ a.down m⟩

/-- Internal actions as equivariant sheaves on the small model. -/
noncomputable def toSite : Equivariant A G ⥤ SiteEquivariant A G where
  obj := toSiteObj
  map := toSiteMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sections of `toSite.obj M` at `X` are the sections of `M` at the underlying
profinite set. -/
theorem toSite_sections (M : Equivariant A G) (X : Model.{u}ᵒᵖ) :
    ((toSite.obj M).obj.val.obj X : Type (u + 1)) =
      sections A M.module ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop) :=
  rfl

/-- Restriction in `toSite.obj M` is restriction in `M`. -/
theorem toSite_map_apply (M : Equivariant A G) {X Y : Model.{u}ᵒᵖ} (f : X ⟶ Y)
    (m : sections A M.module ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)) :
    (toSite.obj M).obj.val.map f m =
      (M.module.X.obj.map ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op).hom m :=
  rfl

/-- The action of `toSite.obj M` is the action of `M`. -/
theorem toSite_act_apply (M : Equivariant A G) (X : Model.{u}ᵒᵖ) (a : (groupPresheaf G).obj X)
    (m : sections A M.module ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)) :
    (toSite.obj M).obj.action.act X a m = M.act _ (groupPresheafObjEquiv G X a) m :=
  rfl

/-- The components of `toSite.map f` are the components of `f`. -/
theorem toSite_map_hom_app {M N : Equivariant A G} (f : M ⟶ N) (X : Model.{u}ᵒᵖ)
    (m : sections A M.module ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)) :
    (toSite.map f).hom.val.app X m =
      (f.val.hom.hom.app (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))).hom m :=
  rfl

/-- Every equivariant map on the small model comes from an equivariant internal map. -/
noncomputable def toSitePreimage {M N : Equivariant A G} (g : toSite.obj M ⟶ toSite.obj N) :
    M ⟶ N :=
  ⟨(InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).preimage
      ⟨{ app S := g.hom.val.app (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S.unop))
         naturality f := g.hom.val.naturality ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).map
            f.unop).op }⟩,
    fun S a m ↦ g.hom.property (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S))
      ((groupPresheafUpEquiv G S) a) m⟩

/-- Reading internal actions on the small model is fully faithful. -/
noncomputable def toSiteFullyFaithful : (toSite (A := A) (G := G)).FullyFaithful where
  preimage := toSitePreimage
  map_preimage g := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X m
    rfl
  preimage_map f := by
    apply Subtype.ext
    apply (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).map_injective
    refine ((InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).map_preimage
      _).trans ?_
    ext S m
    rfl

section Modules

variable (N : SheafOfModules.{u + 1} (siteRing A))

/-- A sheaf of modules on the small model, read on `Profinite`. -/
noncomputable def fromSiteSheaf :
    SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat RingCat)).obj
        (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) A.X)) where
  val := (PresheafOfModules.pushforward₀ (AsSmall.up : Profinite.{u} ⥤ Model.{u}) _).obj N.val
  isSheaf := Functor.op_comp_isSheaf (AsSmall.up : Profinite.{u} ⥤ Model.{u})
    (coherentTopology Profinite.{u}) _ ⟨N.val.presheaf, N.isSheaf⟩

/-- The internal module underlying a sheaf of modules on the small model. -/
noncomputable def fromSiteModule : Modules A :=
  InternalAbelianSheafModule.liftedSheafModule _ A.X (fromSiteSheaf N)

/-- The section module sheaf of `fromSiteModule N` is the transported sheaf. -/
noncomputable def fromSiteIso : (sectionsFunctor A).obj (fromSiteModule N) ≅ fromSiteSheaf N :=
  InternalAbelianSheafModule.sectionModuleFunctor_counit _ A.X _

/-- The sectionwise linear isomorphism given by `fromSiteIso`. -/
noncomputable def fromSiteSectionsEquiv (S : Profinite.{u}) :
    sections A (fromSiteModule N) S ≃ₗ[sectionRing A S]
      N.val.obj (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S)) :=
  ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op S)).mapIso
    (fromSiteIso N)).toLinearEquiv

end Modules

variable (N : SiteEquivariant A G)

/-- The sheaf of modules underlying an equivariant sheaf on the small model. -/
noncomputable abbrev siteSheaf : SheafOfModules.{u + 1} (siteRing A) :=
  (InternalActionSite.forgetSheaf modelPrecoverage.toGrothendieck (siteRing A)).obj N

/-- The action on `fromSiteModule (siteSheaf N)`, conjugated from the action of `N`. -/
noncomputable def fromSiteAct (S : Profinite.{u}) :
    C(S, G) →* Module.End (sectionRing A S) (sections A (fromSiteModule (siteSheaf N)) S) :=
  (fromSiteSectionsEquiv (siteSheaf N) S).symm.conjRingEquiv.toMonoidHom.comp
    ((N.obj.action.act (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S))).comp
      (groupPresheafUpEquiv G S).toMonoidHom)

/-- The conjugated action is computed through the sectionwise isomorphism. -/
theorem fromSiteAct_apply (S : Profinite.{u}) (g : C(S, G))
    (m : sections A (fromSiteModule (siteSheaf N)) S) :
    fromSiteAct N S g m = (fromSiteSectionsEquiv (siteSheaf N) S).symm
      (N.obj.action.act _ ((groupPresheafUpEquiv G S) g)
        (fromSiteSectionsEquiv (siteSheaf N) S m)) :=
  rfl

/-- An equivariant sheaf on the small model, read as an internal action. -/
noncomputable def fromSite : Equivariant A G where
  module := fromSiteModule (siteSheaf N)
  act := fromSiteAct N
  naturality S T f g m := by
    let c := fromSiteIso (siteSheaf N)
    have h1 := PresheafOfModules.naturality_apply c.inv.val f.op
      (N.obj.action.act (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S))
        ((groupPresheafUpEquiv G S) g) (c.hom.val.app (op S) m))
    have h2 := N.obj.action.naturality ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).map f).op
      ((groupPresheafUpEquiv G S) g) (c.hom.val.app (op S) m)
    have h3 := PresheafOfModules.naturality_apply c.hom.val f.op m
    exact h1.symm.trans ((congrArg (c.inv.val.app (op T)) h2).trans
      (congrArg (fun x ↦ c.inv.val.app (op T) (N.obj.action.act _ _ x)) h3.symm))


/-- Reading `fromSite N` on the small model recovers `N`. -/
noncomputable def toSiteFromSiteIso : toSite.obj (fromSite N) ≅ N where
  hom := ObjectProperty.homMk (X := toSite.obj (fromSite N)) (Y := N)
    ⟨{ app X := (fromSiteIso (siteSheaf N)).hom.val.app
          (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))
       naturality f := (fromSiteIso (siteSheaf N)).hom.val.naturality
          ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op },
      fun X a m ↦ (fromSiteSectionsEquiv (siteSheaf N) _).apply_symm_apply _⟩
  inv := ObjectProperty.homMk (X := N) (Y := toSite.obj (fromSite N))
    ⟨{ app X := (fromSiteIso (siteSheaf N)).inv.val.app
          (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))
       naturality f := (fromSiteIso (siteSheaf N)).inv.val.naturality
          ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op },
      fun X a m ↦
        let e := fromSiteSectionsEquiv (siteSheaf N)
          ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)
        congrArg (fun y ↦ e.symm (N.obj.action.act X a y)) (e.apply_symm_apply m).symm⟩
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X m
    exact (fromSiteSectionsEquiv (siteSheaf N) _).symm_apply_apply m
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X m
    exact (fromSiteSectionsEquiv (siteSheaf N) _).apply_symm_apply m

variable (A G) in
/-- Reading internal actions on the small model is an equivalence. -/
instance toSite_isEquivalence : (toSite (A := A) (G := G)).IsEquivalence where
  faithful := toSiteFullyFaithful.faithful
  full := toSiteFullyFaithful.full
  essSurj := ⟨fun N ↦ ⟨fromSite N, ⟨toSiteFromSiteIso N⟩⟩⟩

variable (A G) in
/-- Internal actions of `G` on internal `A`-modules are equivariant sheaves of modules on the
small profinite site, keeping sections, restrictions and actions. -/
noncomputable def siteEquivalence : Equivariant A G ≌ SiteEquivariant A G :=
  (toSite (A := A) (G := G)).asEquivalence

/-- Reading internal actions on the small model is additive. -/
instance toSite_additive : (toSite (A := A) (G := G)).Additive where
  map_add := rfl


section Modules

variable (A)

/-- Internal modules read as sheaves of modules on the small model. -/
noncomputable def toSiteModule : Modules A ⥤ SheafOfModules.{u + 1} (siteRing A) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _).obj
        ((sectionsFunctor A).obj M).val
      isSheaf := Functor.op_comp_isSheaf (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _
        (coherentTopology Profinite.{u}) M.X }
  map f := ⟨(PresheafOfModules.pushforward₀ (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _).map
      ((sectionsFunctor A).map f).val⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction in `(toSiteModule A).obj M` is restriction in `M`. -/
theorem toSiteModule_map_apply (M : Modules A) {X Y : Model.{u}ᵒᵖ} (f : X ⟶ Y)
    (m : sections A M ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)) :
    ((toSiteModule A).obj M).val.map f m =
      (M.X.obj.map ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op).hom m :=
  rfl

/-- The components of `(toSiteModule A).map f` are the components of `f`. -/
theorem toSiteModule_map_val_app {M N : Modules A} (f : M ⟶ N) (X : Model.{u}ᵒᵖ)
    (m : sections A M ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)) :
    ((toSiteModule A).map f).val.app X m =
      (f.hom.hom.app (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))).hom m :=
  rfl

/-- Reading internal modules on the small model is additive. -/
instance toSiteModule_additive : (toSiteModule A).Additive where
  map_add := rfl

/-- Reading internal modules on the small model is fully faithful. -/
noncomputable def toSiteModuleFullyFaithful : (toSiteModule A).FullyFaithful where
  preimage g := (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).preimage
    ⟨{ app S := g.val.app (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S.unop))
       naturality f := g.val.naturality ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).map
          f.unop).op }⟩
  map_preimage g := by
    ext X m
    rfl
  preimage_map f := by
    apply (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).map_injective
    refine ((InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).map_preimage
      _).trans ?_
    ext S m
    rfl

variable {A}

/-- Reading `fromSiteModule N` on the small model recovers `N`. -/
noncomputable def toSiteModuleFromSiteIso (N : SheafOfModules.{u + 1} (siteRing A)) :
    (toSiteModule A).obj (fromSiteModule N) ≅ N where
  hom := ⟨
    { app X := (fromSiteIso N).hom.val.app
        (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))
      naturality f := (fromSiteIso N).hom.val.naturality
        ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op }⟩
  inv := ⟨
    { app X := (fromSiteIso N).inv.val.app
        (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))
      naturality f := (fromSiteIso N).inv.val.naturality
        ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op }⟩
  hom_inv_id := by
    ext X m
    exact (fromSiteSectionsEquiv N _).symm_apply_apply m
  inv_hom_id := by
    ext X m
    exact (fromSiteSectionsEquiv N _).apply_symm_apply m

variable (A)

/-- Reading internal modules on the small model is an equivalence. -/
instance toSiteModule_isEquivalence : (toSiteModule A).IsEquivalence where
  faithful := (toSiteModuleFullyFaithful A).faithful
  full := (toSiteModuleFullyFaithful A).full
  essSurj := ⟨fun N ↦ ⟨fromSiteModule N, ⟨toSiteModuleFromSiteIso N⟩⟩⟩

/-- Internal `A`-modules are sheaves of modules on the small profinite site, keeping
sections and restrictions. -/
noncomputable def moduleSiteEquivalence : Modules A ≌ SheafOfModules.{u + 1} (siteRing A) :=
  (toSiteModule A).asEquivalence

/-- Forgetting the action is compatible with reading on the small model; the components
are identities. -/
noncomputable def toSiteForgetIso :
    toSite ⋙ InternalActionSite.forgetSheaf modelPrecoverage.toGrothendieck (siteRing A) ≅
      forgetAction (A := A) (G := G) ⋙ toSiteModule A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

end Modules

end CategoryTheory.CondensedBar.ActionSite
