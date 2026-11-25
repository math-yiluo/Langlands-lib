/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FixedScalarEtaleModel

/-! # Constant scalar coordinates commute with the small site presentation

Source: Stacks Tags 03CY and 09A5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Reading a constant-ring module as a fixed-scalar sheaf and then in the small
constant-ring model is ordinary small-site precomposition and the normalized scalar
restriction. No complex, derived functor or integral completion occurs.

Source: Stacks Tags 03CY and 09A5, integral-models proof (1)--(2).
(auxiliary; not a blueprint node).

Proof: compose both functors with the fully faithful constant-scalar restriction on
the small site. On the left its counit cancels the inverse restriction used by
fixedScalarProEtaleSheafEquivalence. On the right restriction along a.inv followed by
constant-scalar restriction gives the action of a.inv applied to each constant section.
The normalization of a and its inverse identity identify this with the constant section
on the original site. Thus both resulting functors have identical underlying abelian
sheaves, restriction maps, scalar actions and maps of modules. The identity functions
on sections define mutually inverse natural module morphisms. Lift this natural
isomorphism through the fully faithful restriction functor. The construction also works
for zero rings and empty sites, since it uses no points or nonzero sections.
-/
theorem fixed_scalar_small_coordinates (X : Scheme.{u})
    (k : Type (u + 1)) [CommRing k]
    (a : (sfbModelRings X).obj (adicLisseConstantRing X k) ≅
      ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, u} X) k)
    (ha : ∀ (U : coefficientProEtaleSiteModel.{u, u} X) (r : k),
      a.hom.hom.app (op U)
          ((toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of k))).app
              (op (AsSmall.down.obj U)) r) =
        (toSheafify (coefficientProEtaleModelTopology.{u, u} X)
          ((Functor.const (coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ).obj
            (CommRingCat.of k))).app (op U) r) :
    Nonempty (sfbFixedScalarRestriction X k ⋙
        (fixedScalarProEtaleSheafEquivalence X k).functor ≅
      proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseConstantRing X k)) ⋙
        ConstantCompletion.res a.inv) := by
  let J := coefficientProEtaleModelTopology.{u, u} X
  let down : coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt := AsSmall.down
  let F := down.sheafPushforwardContinuous (ModuleCat.{u + 1} k) J (ProEt.topology X)
  let R := ConstantScalarRestriction.restriction J k
  let P := proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseConstantRing X k))
  let S := ConstantCompletion.res a.inv
  let H := sfbFixedScalarRestriction X k
  have hinv (U : coefficientProEtaleSiteModel.{u, u} X) (r : k) :
      a.inv.hom.app (op U)
          ((toSheafify J ((Functor.const _).obj (CommRingCat.of k))).app (op U) r) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of k))).app
            (op (AsSmall.down.obj U)) r := by
    rw [← ha U r]
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app (op U)) a.hom_inv_id) _
  have hu (U : (coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (r : k) :
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of k)).hom.app U
          ((toSheafify J ((Functor.const _).obj (RingCat.of k))).app U r) =
        (toSheafify J ((Functor.const _).obj (CommRingCat.of k))).app U r := by
    have h := toSheafify_naturality J (Functor.constComp _ (CommRingCat.of k)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv
    change ((toSheafify J ((Functor.const _).obj (RingCat.of k)) ≫
      sheafifyMap J (Functor.constComp _ (CommRingCat.of k)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv ≫
      (sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) _).hom).app U) r = _
    erw [← Category.assoc, ← h, Category.assoc, sheafComposeIso_hom_fac]
    rfl
  let δ : P ⋙ S ⋙ R ≅ H ⋙ F := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · let e (U : (coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) :
          (((P ⋙ S ⋙ R).obj M).obj.obj U) ≅ (((H ⋙ F).obj M).obj.obj U) := by
        refine { hom := ModuleCat.ofHom
                   (X := ((P ⋙ S ⋙ R).obj M).obj.obj U)
                   (Y := ((H ⋙ F).obj M).obj.obj U)
                   { toFun := fun x ↦ x
                     map_add' := fun _ _ ↦ rfl
                     map_smul' := ?_ }
                 inv := ModuleCat.ofHom
                   (X := ((H ⋙ F).obj M).obj.obj U)
                   (Y := ((P ⋙ S ⋙ R).obj M).obj.obj U)
                   { toFun := fun x ↦ x
                     map_add' := fun _ _ ↦ rfl
                     map_smul' := ?_ }
                 hom_inv_id := by ext x; rfl
                 inv_hom_id := by ext x; rfl }
        · intro r x
          let T := M.val.obj (AsSmall.down.op.obj U)
          have h := congrArg (fun z :
              ((adicLisseForget X).obj (adicLisseConstantRing X k)).obj.obj
                (AsSmall.down.op.obj U) ↦ z • (show T from x))
            ((congrArg (a.inv.hom.app U) (hu U r)).trans (hinv U.unop r))
          exact h
        · intro r x
          let T := M.val.obj (AsSmall.down.op.obj U)
          have h := congrArg (fun z :
              ((adicLisseForget X).obj (adicLisseConstantRing X k)).obj.obj
                (AsSmall.down.op.obj U) ↦ z • (show T from x))
            ((congrArg (a.inv.hom.app U) (hu U r)).trans (hinv U.unop r))
          exact h.symm
      exact { hom := ⟨{ app := fun U ↦ (e U).hom
                        naturality := by intros; ext x; rfl }⟩
              inv := ⟨{ app := fun U ↦ (e U).inv
                        naturality := by intros; ext x; rfl }⟩
              hom_inv_id := by ext U x; rfl
              inv_hom_id := by ext U x; rfl }
    · intro M N f
      ext U x
      rfl
  let eR := R.asEquivalence
  let ε : (H ⋙ (fixedScalarProEtaleSheafEquivalence X k).functor) ⋙ R ≅ H ⋙ F :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H
      (Functor.associator F eR.inverse R ≪≫
        Functor.isoWhiskerLeft F eR.counitIso ≪≫ Functor.rightUnitor F)
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful R).whiskeringRight _ |>.preimageIso
    (ε ≪≫ δ.symm)⟩

end AlgebraicGeometry.Scheme
