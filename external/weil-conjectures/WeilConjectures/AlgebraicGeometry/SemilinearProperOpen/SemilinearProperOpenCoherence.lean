/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import Mathlib.Util.AliasIn
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore

/-! # Associativity of the intrinsic semilinear compositors

The constructions, statements and proofs below are retained from the original
mate-pasting module. This file separates their elaboration and artifact generation
from the proper/open pasting proof.

## References

* Stacks Project, Tags 0F7C--0F7F
* Stacks 0F7C--0F7F
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf Functor.mapDerivedCategoryNatIso
  HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors SemilinearSections.systemRing

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

private alias conjugate_transport := SemilinearProperOpenCoreAliases.conjugate_transport

private theorem push_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (M : Modules C τ X) (n : ℕ) (U : Y.ProEt)
    (x : ((push C τ f).obj M).val.obj (op (n, U))) :
    ((eqToIso (congrArg (push C τ) e)).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        (eqToHom (congrArg (fun t ↦ (proEtaleBaseChange t).obj U) e.symm))).op x := by
  cases e
  change x = M.val.map (𝟙 _) x
  rw [PresheafOfModules.map_id]
  rfl

private theorem push_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Modules C τ X} (a : M ⟶ N) (n : ℕ) (U : Y.ProEt)
    (x : ((push C τ f).obj M).val.obj (op (n, U))) :
    (((push C τ f).map a).val.app (op (n, U))) x =
      a.val.app (op (n, (proEtaleBaseChange f).obj U)) x := by
  rfl

private theorem push_obj_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules C τ X) (n : ℕ) {U V : Y.ProEt} (a : U ⟶ V)
    (x : ((push C τ f).obj M).val.obj (op (n, V))) :
    (((push C τ f).obj M).val.map (Prod.mkHom (𝟙 n) a).op) x =
      M.val.map (Prod.mkHom (𝟙 n) ((proEtaleBaseChange f).map a)).op x := by
  rfl

private theorem pushComp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules C τ X) (n : ℕ) (U : Z.ProEt)
    (x : ((push C τ f ⋙ push C τ g).obj M).val.obj (op (n, U))) :
    ((pushComp C τ f g).hom.app M).val.app (op (n, U)) x =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackComp
          (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U)).op x := by
  exact (pushComp_existsUnique C τ f g).choose_spec.1 M n U x

private theorem push_coherence {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (push C τ f) (pushComp C τ g h) ≪≫
        pushComp C τ f (g ≫ h) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pushComp C τ f g) (push C τ h) ≪≫
        pushComp C τ (f ≫ g) h ≪≫
        eqToIso (congrArg (push C τ) (Category.assoc f g h)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  rcases U with ⟨n, U⟩
  ext x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [push_map_apply C τ h ((pushComp C τ f g).hom.app M) n U,
    pushComp_apply C τ f g M n ((proEtaleBaseChange h).obj U),
    pushComp_apply C τ (f ≫ g) h M n U]
  conv_rhs => erw [push_transport C τ (Category.assoc f g h) M n U]
  conv_lhs =>
    erw [pushComp_apply C τ g h ((push C τ f).obj M) n U x,
      pushComp_apply C τ f (g ≫ h) M n U,
      push_obj_map_apply C τ f M n
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g h).hom.app U)]
  apply StrictTower.restriction_pasting M.val _ _ _ _ _ _ x
  apply Prod.hom_ext
  · simp
  · exact StrictTower.site_pasting (P := @WeaklyEtale) (Q := ⊤) f g h U

private theorem pull_coherence {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    pullComp C τ f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (pullComp C τ g h) (pull C τ f) =
      eqToIso (congrArg (pull C τ) (Category.assoc f g h).symm) ≪≫
        pullComp C τ (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (pull C τ h) (pullComp C τ f g) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (ordinaryAdj C τ h) (ordinaryAdj C τ g) (ordinaryAdj C τ f)
    (ordinaryAdj C τ (g ≫ h)) (ordinaryAdj C τ (f ≫ g))
    (ordinaryAdj C τ (f ≫ g ≫ h))
    (pushComp C τ g h) (pushComp C τ f g)
    (pushComp C τ (f ≫ g) h ≪≫
      eqToIso (congrArg (push C τ) (Category.assoc f g h)))
    (pushComp C τ f (g ≫ h)) (push_coherence C τ f g h)
  have ht := StrictTower.mate_transport (pull C τ) (push C τ)
    (fun f ↦ ordinaryAdj C τ f) (ordinaryAdj C τ h)
    (ordinaryAdj C τ (f ≫ g)) (Category.assoc f g h) (pushComp C τ (f ≫ g) h)
  rw [ht] at hh
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hi := congr_app (congrArg Iso.inv hh) M
  simpa only [pullComp, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Iso.symm_inv, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Category.id_comp, Category.comp_id, Category.assoc,
    eqToIso.inv, eqToIso.hom] using hi.symm

private theorem pull_derived_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg (pull C τ) e))).hom =
      (eqToIso (congrArg (P C τ) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem p_coherence {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    pComp C τ f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (pComp C τ g h) (P C τ f) =
      eqToIso (congrArg (P C τ) (Category.assoc f g h).symm) ≪≫
        pComp C τ (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (P C τ h) (pComp C τ f g) := by
  have hh := StrictTower.descend_coherence (pull C τ h) (pull C τ g) (pull C τ f)
    (pull C τ (g ≫ h)) (pull C τ (f ≫ g))
    (pull C τ (f ≫ g ≫ h)) (pull C τ ((f ≫ g) ≫ h))
    (pullComp C τ g h) (pullComp C τ f g)
    (pullComp C τ f (g ≫ h)) (pullComp C τ (f ≫ g) h)
    (eqToIso (congrArg (pull C τ) (Category.assoc f g h).symm))
    (pull_coherence C τ f g h)
  rw [pull_derived_transport C τ (Category.assoc f g h).symm] at hh
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [pComp, P, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Functor.map_comp] using congr_app hh M

private theorem jComp_transport {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion k] (e : f ≫ g = k) :
    Adjunction.leftAdjointCompIso (jAdj C τ f) (jAdj C τ g) (jAdj C τ k)
        ((pComp C τ f g).symm ≪≫ eqToIso (congrArg (P C τ) e)) =
      jComp C τ f g ≪≫ jCongr C τ e := by
  subst k
  simp only [jCongr, eqToIso_refl, Iso.trans_refl, jComp]

/-- Coherence of the specified compositors makes iterated pasting independent of
parenthesization, for inverse image, its right-adjoint mate, and open extension. -/
theorem compositor_associativity :
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (M : Derived C τ T),
      (pComp C τ (f ≫ g) h).hom.app M ≫
        (pComp C τ f g).hom.app ((P C τ h).obj M) =
      (eqToIso (congrArg (P C τ) (Category.assoc f g h))).hom.app M ≫
        (pComp C τ f (g ≫ h)).hom.app M ≫
        (P C τ f).map ((pComp C τ g h).hom.app M)) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      (M : Derived C τ X),
      (R C τ h).map ((sComp C τ f g).hom.app M) ≫
        (sComp C τ (f ≫ g) h).hom.app M =
      (sComp C τ g h).hom.app ((R C τ f).obj M) ≫
        (sComp C τ f (g ≫ h)).hom.app M ≫
        (eqToIso (congrArg (R C τ) (Category.assoc f g h))).inv.app M) ∧
    (∀ {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
      [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
      (M : Derived C τ X),
      (J C τ h).map ((jComp C τ f g).hom.app M) ≫
        (jComp C τ (f ≫ g) h).hom.app M =
      (jComp C τ g h).hom.app ((J C τ f).obj M) ≫
        (jComp C τ f (g ≫ h)).hom.app M ≫
        (jCongr C τ (Category.assoc f g h)).inv.app M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z T f g h M
    have hp := congr_app (congrArg Iso.hom (p_coherence C τ f g h)) M
    have hp' := congrArg (fun q ↦
      (eqToIso (congrArg (P C τ) (Category.assoc f g h))).hom.app M ≫ q) hp
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, eqToIso.hom, eqToIso.inv, eqToHom_trans_assoc,
      eqToHom_refl, NatTrans.id_app, Category.id_comp] using hp'.symm
  · intro X Y Z T f g h M
    have hp := congrArg Iso.hom (p_coherence C τ f g h)
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom] at hp
    have hh := StrictTower.conjugate_triangle_assoc (adj C τ h) (adj C τ g) (adj C τ f)
      (adj C τ (g ≫ h)) (adj C τ (f ≫ g)) (adj C τ (f ≫ g ≫ h))
      (pComp C τ g h) (pComp C τ f g)
      (eqToIso (congrArg (P C τ) (Category.assoc f g h).symm) ≪≫
        pComp C τ (f ≫ g) h) (pComp C τ f (g ≫ h))
      (by simpa only [Iso.trans_hom, Category.assoc] using hp.symm)
    have ht := congrArg Iso.hom (conjugate_transport (P C τ) (R C τ)
      (fun f ↦ adj C τ f) ((adj C τ h).comp (adj C τ (f ≫ g)))
      (Category.assoc f g h) (pComp C τ (f ≫ g) h))
    simp only [Iso.trans_hom, conjugateIsoEquiv_apply_hom] at ht
    simp only [Iso.trans_hom] at hh
    rw [ht] at hh
    have hm := congr_app hh M
    apply (cancel_mono
      ((eqToIso (congrArg (R C τ) (Category.assoc f g h))).hom.app M)).1
    simpa only [sComp, conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id] using hm.symm
  · intro X Y Z T f g h _ _ _ M
    have hi : Functor.isoWhiskerLeft (P C τ h) (pComp C τ f g).symm ≪≫
        ((pComp C τ (f ≫ g) h).symm ≪≫
          eqToIso (congrArg (P C τ) (Category.assoc f g h))) =
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (pComp C τ g h).symm (P C τ f) ≪≫
          (pComp C τ f (g ≫ h)).symm := by
      have hp := congrArg Iso.symm (p_coherence C τ f g h)
      apply Iso.ext
      apply NatTrans.ext
      funext N
      simpa only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.associator_inv_app, Category.id_comp, Category.assoc,
        Iso.symm_hom, eqToIso.inv, eqToIso.hom] using
          (congr_app (congrArg Iso.hom hp) N).symm
    have hh := Adjunction.leftAdjointCompIso_assoc
      (jAdj C τ f) (jAdj C τ g) (jAdj C τ h)
      (jAdj C τ (f ≫ g)) (jAdj C τ (g ≫ h)) (jAdj C τ (f ≫ g ≫ h))
      (pComp C τ f g).symm (pComp C τ g h).symm
      (pComp C τ f (g ≫ h)).symm
      ((pComp C τ (f ≫ g) h).symm ≪≫
        eqToIso (congrArg (P C τ) (Category.assoc f g h))) hi
    rw [jComp_transport C τ (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    apply (cancel_mono ((jCongr C τ (Category.assoc f g h)).hom.app M)).1
    simpa only [jComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hm.symm

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace SemilinearProperOpenCoherenceAliases
private alias push_transport := AlgebraicGeometry.ProEtale.SemilinearProperOpen.push_transport
private alias push_map_apply := AlgebraicGeometry.ProEtale.SemilinearProperOpen.push_map_apply
private alias push_obj_map_apply :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.push_obj_map_apply
private alias pushComp_apply := AlgebraicGeometry.ProEtale.SemilinearProperOpen.pushComp_apply
private alias push_coherence := AlgebraicGeometry.ProEtale.SemilinearProperOpen.push_coherence
private alias pull_coherence := AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_coherence
private alias pull_derived_transport :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.pull_derived_transport
private alias p_coherence := AlgebraicGeometry.ProEtale.SemilinearProperOpen.p_coherence
private alias jComp_transport := AlgebraicGeometry.ProEtale.SemilinearProperOpen.jComp_transport
end SemilinearProperOpenCoherenceAliases
