/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedBar.CondensedEquivariantBarData

/-! # Restriction of scalars on internal condensed actions

Restricting scalars along a ring map `a : A ⟶ A'` keeps the underlying abelian sheaf and
the section action; an `A'`-linear section endomorphism is `A`-linear for the restricted
section-module structure. This realizes the specification `ScalarAction a G`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.CondensedBar

variable {A A' : Ring.{u}} (a : A ⟶ A')

/-- The section-module structure of a restricted module is restriction of scalars along the
section ring map induced by `a`. -/
theorem smul_comap_sections (N : Modules A') (S : Profinite.{u}) (r : sectionRing A S)
    (x : sections A ((Mod.comap a.hom.hom).obj N) S) (r' : sectionRing A' S)
    (x' : sections A' N S) (hr : r' = (a.hom.hom.hom.app (op S)).hom r) (hx : x' = x) :
    r • x = r' • x' := by
  subst hr hx
  have h := ConcreteCategory.congr_hom (congr_app (Functor.LaxMonoidal.μ_natural_left
    (sheafToPresheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}) a.hom.hom N.X)
      (op S)) (r ⊗ₜ[ℤ] x')
  exact (congrArg (fun y ↦ ((Mod.act N.X).hom.app (op S)).hom y) h).symm

/-- An `A'`-linear endomorphism of the sections of `N` is `A`-linear on the sections of the
restricted module; this is a monoid map of endomorphism monoids. -/
def restrictSectionEnd (N : Modules A') (S : Profinite.{u}) :
    Module.End (sectionRing A' S) (sections A' N S) →*
      Module.End (sectionRing A S) (sections A ((Mod.comap a.hom.hom).obj N) S) where
  toFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' r x :=
        (congrArg f (smul_comap_sections a N S r x _ x rfl rfl)).trans
          ((f.map_smul _ x).trans (smul_comap_sections a N S r (f x) _ (f x) rfl rfl).symm) }
  map_one' := rfl
  map_mul' _ _ := rfl

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction of scalars on internal actions: restrict the module, keep the action. -/
def scalarActionFunctor : Equivariant A' G ⥤ Equivariant A G where
  obj N :=
    { module := (Mod.comap a.hom.hom).obj N.module
      act := fun S ↦ (restrictSectionEnd a N.module S).comp (N.act S)
      naturality := N.naturality }
  map f := ⟨(Mod.comap a.hom.hom).map f.val, f.property⟩

/-- The canonical realization of scalar restriction on internal actions, with identity
underlying comparison. -/
def scalarActionOfComap : ScalarAction a G where
  functor := scalarActionFunctor a G
  additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  underlying := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  action _ _ _ _ := rfl

/-- Scalar restriction on internal actions exists. -/
theorem nonempty_scalarAction : Nonempty (ScalarAction a G) :=
  ⟨scalarActionOfComap a G⟩

end CategoryTheory.CondensedBar
