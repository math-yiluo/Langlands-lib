/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction

/-!
# Section coordinates for intrinsic constant coefficients

## References

* Stacks Project, Tags 00YV and 09AE
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- An isomorphism of fixed-scalar sheaves identifies their additive section groups. -/
noncomputable def fixedSectionEquiv (R : Type (u + 1)) [Ring R]
    {X : AlgebraicGeometry.Scheme.{u}}
    {F G : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)}
    (e : F ≅ G) (Q : X.ProEtᵒᵖ) : F.obj.obj Q ≃+ G.obj.obj Q :=
  (CategoryTheory.Iso.toLinearEquiv
    { hom := e.hom.hom.app Q
      inv := e.inv.hom.app Q
      hom_inv_id := congrArg (fun f ↦ f.hom.app Q) e.hom_inv_id
      inv_hom_id := congrArg (fun f ↦ f.hom.app Q) e.inv_hom_id }).toAddEquiv

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- The scalar sheafification unit on a fixed-scalar sheaf. -/
noncomputable def sfRealizationUnit (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.app
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).obj F.obj)

/-- The realization unit is invertible because its source is already a sheaf. -/
instance sfRealizationUnit_isIso (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsIso (sfRealizationUnit A X F) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
  change IsIso (toSheafify (ProEt.topology X)
    (F.obj ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1}))
  apply isIso_toSheafify
  exact ((sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj F).property

/-- The canonical realization identifies section groups by its sheafification unit. -/
noncomputable def sfRealizationSectionEquiv (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (Q : X.ProEtᵒᵖ) : F.obj.obj Q ≃+
      ((sfIntrinsicModuleEquivalence X A).functor.obj F).val.obj Q :=
  { toFun := (sfRealizationUnit A X F).app Q
    invFun := (inv (sfRealizationUnit A X F)).app Q
    left_inv x := by
      have h := congrArg (fun f ↦ f.app Q x) (IsIso.hom_inv_id (sfRealizationUnit A X F))
      exact h
    right_inv x := by
      have h := congrArg (fun f ↦ f.app Q x) (IsIso.inv_hom_id (sfRealizationUnit A X F))
      exact h
    map_add' := map_add ((sfRealizationUnit A X F).app Q).hom }

/-- Realization section coordinates commute with sheaf morphisms. -/
theorem sfRealizationSectionEquiv_map (X : Scheme.{u})
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : F ⟶ G) (Q : X.ProEtᵒᵖ) (x : F.obj.obj Q) :
    sfRealizationSectionEquiv A X G Q (f.hom.app Q x) =
      ((sfIntrinsicModuleEquivalence X A).functor.map f).val.app Q
        (sfRealizationSectionEquiv A X F Q x) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.naturality
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).map f.hom)
  exact congrArg (fun g ↦ g.app Q x) h

/-- Every intrinsic section has canonical fixed-scalar coordinates, with the equivalence
counit taking realization back to the specified sheaf. -/
noncomputable def sfIntrinsicSectionEquiv (X : Scheme.{u})
    (N : proEtaleRingModules X (proEtaleConstantRing X A)) (Q : X.ProEtᵒᵖ) :
    ((sfIntrinsicModuleEquivalence X A).inverse.obj N).obj.obj Q ≃+ N.val.obj Q :=
  (sfRealizationSectionEquiv A X _ Q).trans
    { toFun := ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app N).val.app Q
      invFun := ((sfIntrinsicModuleEquivalence X A).counitIso.inv.app N).val.app Q
      left_inv x := by
        exact congrArg (fun f ↦ f.val.app Q x)
          ((sfIntrinsicModuleEquivalence X A).counitIso.hom_inv_id_app N)
      right_inv x := by
        exact congrArg (fun f ↦ f.val.app Q x)
          ((sfIntrinsicModuleEquivalence X A).counitIso.inv_hom_id_app N)
      map_add' := map_add _ }

private noncomputable def counitSourceIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (sfIntrinsicModuleEquivalence X A).functor.obj
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
        ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          ((sfIntrinsicModuleEquivalence X A).inverse.obj N))) ≅
      (sfIntrinsicExtensionByZero j A).obj ((sfIntrinsicOpenRestriction j A).obj N) :=
  (sfIntrinsicModuleEquivalence X A).functor.mapIso
    ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapIso
      ((sfIntrinsicModuleEquivalence U A).unitIso.app _))

private theorem counitSourceIso_comp {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (counitSourceIso A j N).hom ≫ (sfIntrinsicExtensionByZeroAdjunction j A).counit.app N =
      (sfIntrinsicModuleEquivalence X A).functor.map
        ((ProEtale.openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).counit.app
            ((sfIntrinsicModuleEquivalence X A).inverse.obj N)) ≫
        (sfIntrinsicModuleEquivalence X A).counitIso.hom.app N := by
  dsimp only [sfIntrinsicExtensionByZeroAdjunction]
  rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app]
  dsimp only [counitSourceIso, Functor.mapIso_hom]
  let L := ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let R := (ProEtale.openImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
      ((sfIntrinsicModuleEquivalence X A).inverse.obj N)
  let c := (ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).counit.app
      ((sfIntrinsicModuleEquivalence X A).inverse.obj N)
  change (sfIntrinsicModuleEquivalence X A).functor.map
      (L.map ((sfIntrinsicModuleEquivalence U A).unitIso.app R).hom) ≫
    ((sfIntrinsicModuleEquivalence X A).functor.map
      (L.map ((sfIntrinsicModuleEquivalence U A).unitIso.app R).inv ≫ c) ≫
      (sfIntrinsicModuleEquivalence X A).counitIso.hom.app N) = _
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [L.map_id, Category.id_comp]

/-- Fixed-scalar and intrinsic open counits have isomorphic source section groups;
the comparison intertwines their specified counits. This follows by expanding the
composite adjunction counit and cancelling the realization unit with its inverse. -/
theorem sfIntrinsicCounit_section_coordinates {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : proEtaleRingModules X (proEtaleConstantRing X A))
    (Q : X.ProEtᵒᵖ) :
    ∃ e :
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
        ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          ((sfIntrinsicModuleEquivalence X A).inverse.obj N))).obj.obj Q ≃+
        ((sfIntrinsicExtensionByZero j A).obj
          ((sfIntrinsicOpenRestriction j A).obj N)).val.obj Q,
      ∀ x, ((sfIntrinsicExtensionByZeroAdjunction j A).counit.app N).val.app Q (e x) =
        sfIntrinsicSectionEquiv A X N Q
          (((ProEtale.openImmersionLowerShriekAdjunction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).counit.app
              ((sfIntrinsicModuleEquivalence X A).inverse.obj N)).hom.app Q x) := by
  let e := counitSourceIso A j N
  let e' :
      ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((sfIntrinsicModuleEquivalence X A).inverse.obj N)))).val.obj Q ≃+
        ((sfIntrinsicExtensionByZero j A).obj ((sfIntrinsicOpenRestriction j A).obj N)).val.obj Q :=
    { toFun := e.hom.val.app Q
      invFun := e.inv.val.app Q
      left_inv x := congrArg (fun f ↦ f.val.app Q x) e.hom_inv_id
      right_inv x := congrArg (fun f ↦ f.val.app Q x) e.inv_hom_id
      map_add' := map_add _ }
  refine ⟨(sfRealizationSectionEquiv A X _ Q).trans e', ?_⟩
  intro x
  have h := congrArg (fun f ↦ f.val.app Q
    (sfRealizationSectionEquiv A X _ Q x)) (counitSourceIso_comp A j N)
  change _ = ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app N).val.app Q
    (((sfIntrinsicModuleEquivalence X A).functor.map _).val.app Q _) at h
  exact h.trans (congrArg
    (fun z ↦ ((sfIntrinsicModuleEquivalence X A).counitIso.hom.app N).val.app Q z)
    (sfRealizationSectionEquiv_map A X
      ((ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).counit.app
          ((sfIntrinsicModuleEquivalence X A).inverse.obj N)) Q x).symm)

/-- Conjugating an open counit by a specified realization isomorphism gives a
commuting square of additive section groups. Apply the preceding counit comparison
and then counit naturality to the specified fixed-scalar isomorphism. -/
theorem sfIntrinsicCounit_conjugation {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (N : proEtaleRingModules X (proEtaleConstantRing X A))
    (H : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (e : H ≅ (sfIntrinsicModuleEquivalence X A).inverse.obj N) (Q : X.ProEtᵒᵖ) :
    ∃ eC :
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
        ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
          H)).obj.obj Q ≃+
        ((sfIntrinsicExtensionByZero j A).obj
          ((sfIntrinsicOpenRestriction j A).obj N)).val.obj Q,
      ∀ x, ((sfIntrinsicExtensionByZeroAdjunction j A).counit.app N).val.app Q (eC x) =
        sfIntrinsicSectionEquiv A X N Q
          (ProEtale.fixedSectionEquiv (ULift.{u + 1, u} A) e Q
            (((ProEtale.openImmersionLowerShriekAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).counit.app H).hom.app Q x)) := by
  obtain ⟨eN, heN⟩ := sfIntrinsicCounit_section_coordinates A j N Q
  let e' := ((ProEtale.openImmersionRestriction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j) ⋙
      ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapIso e
  refine ⟨(ProEtale.fixedSectionEquiv (ULift.{u + 1, u} A) e' Q).trans eN, ?_⟩
  intro x
  refine (heN ((ProEtale.fixedSectionEquiv (ULift.{u + 1, u} A) e' Q) x)).trans ?_
  apply congrArg (sfIntrinsicSectionEquiv A X N Q)
  exact (congrArg (fun f ↦ f.hom.app Q x)
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).counit.naturality e.hom))

end AlgebraicGeometry.Scheme
