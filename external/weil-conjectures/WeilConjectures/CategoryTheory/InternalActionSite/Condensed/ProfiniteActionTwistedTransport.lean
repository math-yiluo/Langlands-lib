/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionEquivalence
public import WeilConjectures.CategoryTheory.InternalActionSite.PresentationSections
public import WeilConjectures.CategoryTheory.InternalActionSite.ProjectionRingedTopos
public import WeilConjectures.CategoryTheory.CondensedBar.CondensedScalarAction

/-!
# Internal condensed actions as modules on the twisted ringed site

Source: paragraph (3) of the direct-image stability proof, action-site presentation
(blueprint: def-sfb-condensed-derived-invariants).

Composing `siteEquivalence` with an action-site presentation identifies internal actions
of `G` on internal `A`-modules with modules over the twisted ring on the twisted small
profinite site. Under this identification, scalar restriction of actions along `a : A ⟶ A'`
is restriction of scalars along the induced map of twisted rings, and the trivial action is
pullback along the projection to the small profinite site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar.ActionSite

open InternalActionSite

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The twisted small profinite site of `G`. -/
abbrev twistedTopology : GrothendieckTopology (Object (groupPresheaf G)) :=
  topology (groupPresheaf G) modelPrecoverage.{u}

variable (A : Ring.{u})

/-- The twisted coefficient ring of `A` on the twisted small profinite site. -/
noncomputable abbrev twistedRingOf : Sheaf (twistedTopology G) RingCat.{u + 1} :=
  twistedRing (groupPresheaf G) modelPrecoverage modelPrecoverage_isSiteForCoverings
    (ringSheaf A)

/-- A chosen action-site presentation on the small profinite site. -/
noncomputable def presentationOf :
    Presentation (groupPresheaf G) modelPrecoverage modelPrecoverage_isSiteForCoverings
      (ringSheaf A) :=
  Classical.choice (presentation (groupPresheaf G) modelPrecoverage
    modelPrecoverage_isSiteForCoverings (groupPresheaf_isSheaf G) (ringSheaf A))

/-- Internal actions are modules over the twisted ring. -/
noncomputable def twistedEquivalence :
    Equivariant A G ≌ SheafOfModules.{u + 1} (twistedRingOf G A) :=
  (siteEquivalence A G).trans (presentationOf G A).sheafEquivalence

instance twistedEquivalence_functor_additive : (twistedEquivalence G A).functor.Additive := by
  have := (presentationOf G A).sheaf_additive
  exact inferInstanceAs (toSite ⋙ (presentationOf G A).sheafEquivalence.functor).Additive

variable {A G}

/-- The ring sheaf map on the small model induced by a map of condensed rings. -/
noncomputable def ringSheafMap {A A' : Ring.{u}} (a : A ⟶ A') : ringSheaf A ⟶ ringSheaf A' :=
  ⟨Functor.whiskerLeft (AsSmall.down : Model.{u} ⥤ Profinite.{u}).op
    (Functor.whiskerRight ((Monoidal.commMonFunctorCategoryEquivalence _ _).functor.map
      ((sheafToPresheaf _ _).mapCommMon.map a)) InternalAbelianSheafModule.commMonToRing)⟩

variable (G) in
/-- The map of twisted coefficient rings induced by a map of condensed rings. -/
noncomputable def twistedRingMap {A A' : Ring.{u}} (a : A ⟶ A') :
    twistedRingOf G A ⟶ twistedRingOf G A' :=
  (sheafCompose (twistedTopology G) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ⟨Functor.whiskerLeft (projection (groupPresheaf G)).op (ringSheafMap a).hom⟩

/-- Sections of the twisted module of an internal action are its sections. -/
noncomputable def twistedSections (M : Equivariant A G) (X : Model.{u}) :
    ((twistedEquivalence G A).functor.obj M).val.obj (op (Object.mk X)) ≃ₗ[
      sectionRing A (AsSmall.down.obj X)] sections A M.module (AsSmall.down.obj X) :=
  (presentationOf G A).sheafSections (toSite.obj M) X

theorem twistedSections_restriction (M : Equivariant A G) {X Y : Model.{u}} (f : X ⟶ Y)
    (g : (groupPresheaf G).obj (op X))
    (m : ((twistedEquivalence G A).functor.obj M).val.obj (op (Object.mk Y))) :
    twistedSections M X (((twistedEquivalence G A).functor.obj M).val.map
      (opArrow (groupPresheaf G) f g) m) =
      M.act (AsSmall.down.obj X) g.down
        ((M.module.X.obj.map (AsSmall.down.map f).op).hom (twistedSections M Y m)) :=
  (presentationOf G A).sheafSections_restriction (toSite.obj M) f g m

theorem twistedSections_naturality {M N : Equivariant A G} (φ : M ⟶ N) (X : Model.{u})
    (m : ((twistedEquivalence G A).functor.obj M).val.obj (op (Object.mk X))) :
    twistedSections N X (((twistedEquivalence G A).functor.map φ).val.app _ m) =
      (φ.val.hom.hom.app (op (AsSmall.down.obj X))).hom (twistedSections M X m) :=
  (presentationOf G A).sheafSections_naturality (toSite.map φ) X m

section Scalar

variable {A A' : Ring.{u}} (a : A ⟶ A')

/-- Sectionwise, the twisted module of a scalar restriction is the restriction of scalars of
the twisted module. -/
noncomputable def scalarTwistedSections (N : Equivariant A' G) (X : Model.{u}) :
    ((twistedEquivalence G A).functor.obj ((scalarActionFunctor a G).obj N)).val.obj
        (op (Object.mk X)) ≃ₗ[(siteRing A).obj.obj (op X)]
      ((SheafOfModules.restrictScalars (twistedRingMap G a)).obj
        ((twistedEquivalence G A').functor.obj N)).val.obj (op (Object.mk X)) where
  toFun m := (twistedSections N X).symm (twistedSections ((scalarActionFunctor a G).obj N) X m)
  invFun y := (twistedSections ((scalarActionFunctor a G).obj N) X).symm (twistedSections N X y)
  map_add' m m' := by
    rw [map_add, map_add]
  map_smul' r m := by
    rw [LinearEquiv.map_smul, smul_comap_sections a N.module _ r _ _ _ rfl rfl,
      LinearEquiv.map_smul]
    rfl
  left_inv m := by
    simp
  right_inv y := by
    simp

theorem scalarTwistedSections_apply (N : Equivariant A' G) (X : Model.{u}) (m) :
    twistedSections N X (scalarTwistedSections a N X m) =
      twistedSections ((scalarActionFunctor a G).obj N) X m :=
  (twistedSections N X).apply_symm_apply _

theorem scalarTwistedSections_restriction (N : Equivariant A' G) {X Y : Model.{u}} (f : X ⟶ Y)
    (g : (groupPresheaf G).obj (op X))
    (m : ((twistedEquivalence G A).functor.obj ((scalarActionFunctor a G).obj N)).val.obj
      (op (Object.mk Y))) :
    scalarTwistedSections a N X (((twistedEquivalence G A).functor.obj
      ((scalarActionFunctor a G).obj N)).val.map (opArrow (groupPresheaf G) f g) m) =
      ((twistedEquivalence G A').functor.obj N).val.map (opArrow (groupPresheaf G) f g)
        (scalarTwistedSections a N Y m) := by
  apply (twistedSections N X).injective
  rw [scalarTwistedSections_apply, twistedSections_restriction, twistedSections_restriction,
    scalarTwistedSections_apply]
  rfl

/-- The twisted module of a scalar restriction is the restriction of scalars of the twisted
module. -/
noncomputable def scalarTwistedIso (N : Equivariant A' G) :
    (twistedEquivalence G A).functor.obj ((scalarActionFunctor a G).obj N) ≅
      (SheafOfModules.restrictScalars (twistedRingMap G a)).obj
        ((twistedEquivalence G A').functor.obj N) :=
  twistedIsoMk (scalarTwistedSections a N) (fun f g m ↦ scalarTwistedSections_restriction a N f g m)

theorem scalarTwistedIso_naturality {N N' : Equivariant A' G} (φ : N ⟶ N') :
    (twistedEquivalence G A).functor.map ((scalarActionFunctor a G).map φ) ≫
        (scalarTwistedIso a N').hom =
      (scalarTwistedIso a N).hom ≫
        (SheafOfModules.restrictScalars (twistedRingMap G a)).map
          ((twistedEquivalence G A').functor.map φ) := by
  apply twisted_hom_ext
  intro X m
  apply (twistedSections N' X).injective
  have h₁ := scalarTwistedSections_apply a N' X
    (((twistedEquivalence G A).functor.map ((scalarActionFunctor a G).map φ)).val.app _ m)
  have h₂ := twistedSections_naturality φ X (scalarTwistedSections a N X m)
  have h₃ := twistedSections_naturality ((scalarActionFunctor a G).map φ) X m
  rw [scalarTwistedSections_apply] at h₂
  exact h₁.trans (h₃.trans h₂.symm)

/-- Scalar restriction of actions is restriction of scalars on twisted modules. -/
noncomputable def scalarTwistedNatIso :
    scalarActionFunctor a G ⋙ (twistedEquivalence G A).functor ≅
      (twistedEquivalence G A').functor ⋙
        SheafOfModules.restrictScalars (twistedRingMap G a) :=
  NatIso.ofComponents (scalarTwistedIso a) (scalarTwistedIso_naturality a)

end Scalar

section Trivial

variable (A G)

/-- Pullback along the projection from the twisted small profinite site. -/
noncomputable abbrev projectionPullback :
    SheafOfModules.{u + 1} (siteRing A) ⥤ SheafOfModules.{u + 1} (twistedRingOf G A) :=
  trivialPullback (groupPresheaf G) modelPrecoverage modelPrecoverage_isSiteForCoverings
    (ringSheaf A)

/-- The trivial action functor. -/
noncomputable abbrev trivialAction : Modules A ⥤ Equivariant A G :=
  Profinite.CondensedAction.trivial (R := A.toMon) (P := G)

variable {A G}

/-- Sectionwise, the twisted module of a trivial action is the pullback along the
projection. -/
noncomputable def trivialTwistedSections (M : Modules A) (X : Model.{u}) :
    ((twistedEquivalence G A).functor.obj ((trivialAction G A).obj M)).val.obj
        (op (Object.mk X)) ≃ₗ[(siteRing A).obj.obj (op X)]
      ((projectionPullback G A).obj ((moduleSiteEquivalence A).functor.obj M)).val.obj
        (op (Object.mk X)) where
  toFun m := twistedSections ((trivialAction G A).obj M) X m
  invFun y := (twistedSections ((trivialAction G A).obj M) X).symm y
  map_add' m m' := map_add _ m m'
  map_smul' r m := (twistedSections ((trivialAction G A).obj M) X).map_smul r m
  left_inv m := (twistedSections ((trivialAction G A).obj M) X).symm_apply_apply m
  right_inv y := (twistedSections ((trivialAction G A).obj M) X).apply_symm_apply y

/-- The twisted module of a trivial action is the pullback along the projection. -/
noncomputable def trivialTwistedIso (M : Modules A) :
    (twistedEquivalence G A).functor.obj ((trivialAction G A).obj M) ≅
      (projectionPullback G A).obj ((moduleSiteEquivalence A).functor.obj M) :=
  twistedIsoMk (trivialTwistedSections M) (fun f g m ↦
    twistedSections_restriction ((trivialAction G A).obj M) f g m)

theorem trivialTwistedIso_naturality {M M' : Modules A} (φ : M ⟶ M') :
    (twistedEquivalence G A).functor.map ((trivialAction G A).map φ) ≫ (trivialTwistedIso M').hom =
      (trivialTwistedIso M).hom ≫
        (projectionPullback G A).map ((moduleSiteEquivalence A).functor.map φ) := by
  apply twisted_hom_ext
  intro X m
  exact twistedSections_naturality ((trivialAction G A).map φ) X m

/-- The trivial action is pullback along the projection on twisted modules. -/
noncomputable def trivialTwistedNatIso :
    trivialAction G A ⋙ (twistedEquivalence G A).functor ≅
      (moduleSiteEquivalence A).functor ⋙ projectionPullback G A :=
  NatIso.ofComponents trivialTwistedIso trivialTwistedIso_naturality

end Trivial

end CategoryTheory.CondensedBar.ActionSite
