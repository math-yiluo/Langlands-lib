/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.GlobalSectionsDirectImageKInjectiveAcyclic

/-! # Derived global sections after affinization

Source: Stacks Project, Cohomology, Lemma 20.28.2, Tag 0D5T,
and the construction of derived global sections in Section 20.28, Tag 079V.
(blueprint: lem-pc-derived-global-sections-affinization-comparison).
-/

@[expose] public section

universe u wX wY wA
open CategoryTheory Opposite
namespace AlgebraicGeometry

private noncomputable def underived_comparison (X : Scheme.{u}) :
    RingedSpace.moduleDirectImage X.toSpecΓ.toLRSHom.toShHom ⋙
      (RingedSpace.globalSectionsFunctor (Spec Γ(X, ⊤)).toRingedSpace ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom) ≅
      RingedSpace.globalSectionsFunctor X.toRingedSpace := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · change (ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom).obj
      ((ModuleCat.restrictScalars X.toSpecΓ.appTop.hom).obj (M.val.obj (op ⊤))) ≅
      M.val.obj (op ⊤)
    exact (ModuleCat.restrictScalarsComp _ _).symm.app _ ≪≫
      (ModuleCat.restrictScalarsId' _ (by
        rw [← CommRingCat.hom_comp, Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
        rfl)).app _
  · intro M N f
    apply ModuleCat.hom_ext
    rfl

/-- Derived global sections factors through derived pushforward to the spectrum of
its own coefficient ring. The ring isomorphism `ΓSpecIso` supplies the scalar transport.
Source: Stacks Project, Cohomology, Lemma 20.28.2
(lemma-derived-pushforward-composition, Tag 0D5T), and Section 20.28 (Tag 079V).
(blueprint: lem-pc-derived-global-sections-affinization-comparison).
Proof: Put A = Γ(X,O_X), Y = Spec A, and a = X.toSpecΓ. Let P be the one-point
ringed space with ring A. The morphism b:Y → P has ring map A → Γ(Y,O_Y)
given by ΓSpecIso.inv. The identity ΓSpecIso.inv followed by a.appTop = id_A
identifies b composed with a with the global-sections morphism p:X → P;
this includes the empty open, where the ring sheaf is zero. By Tag 0D5T,
Rb_* composed with Ra_* is naturally isomorphic to Rp_*. Evaluating module
sheaves on P at its whole space is an exact equivalence with A-modules.
Under this equivalence Rp_* is RΓ(X,-), while Rb_* is the right derived
functor of Γ(Y,-) followed by restriction along ΓSpecIso.inv. Exactness of
the point equivalence lets it commute with the derived construction. Compose
these natural isomorphisms and invert to obtain the displayed orientation.
All comparisons come from derived adjunctions and their units, so are natural
on every unbounded derived object, including zero objects. No quasi-coherence,
compactness or flatness of a is required. -/
theorem derivedGlobalSections_affinization_comparison (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))]
    [HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))] :
    letI : HasDerivedCategory.{wA} (ModuleCat.{u} Γ(X, ⊤)) :=
      inferInstanceAs (HasDerivedCategory.{wA}
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))
    Nonempty ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ≅
      schemeDerivedDirectImage X.toSpecΓ ⋙
        (RingedSpace.globalSectionsFunctor (Spec Γ(X, ⊤)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom).rightDerivedFunctor) := by
  let : HasDerivedCategory.{wA} (ModuleCat.{u} Γ(X, ⊤)) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))))
  have : (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive :=
    RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let F := RingedSpace.moduleDirectImage X.toSpecΓ.toLRSHom.toShHom
  let G := RingedSpace.globalSectionsFunctor (Spec Γ(X, ⊤)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom
  let β := Functor.rightDerivedFunctorCompUnit F G
  have hβ : (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun J ↦ ?_)
    obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
    change IsIso (β.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
    have h₁ : IsIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := inferInstance
    have h₂ : IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
      isIso_globalSections_restrictScalars_unit_on_directImage_kInjective
        X.toSpecΓ (Scheme.ΓSpecIso Γ(X, ⊤)).inv I
    dsimp only [β, Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  let e := Functor.rightDerivedUnique (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit β
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
  exact ⟨(Functor.rightDerivedFunctorNatIso (underived_comparison X)).symm ≪≫ e⟩

end AlgebraicGeometry
