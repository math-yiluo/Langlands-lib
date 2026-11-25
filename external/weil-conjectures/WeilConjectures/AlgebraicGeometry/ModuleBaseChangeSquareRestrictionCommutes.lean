/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Components of module base change under restriction

Source: Stacks Project, Sheaves, Tag 00A0 and Cohomology, Tags 0ATL and 0ATM.
(blueprint: lem-weil-pbc-module-square-restriction-commutes).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

private def baseChangeMapCore {X S T X₁ : Scheme.{u}}
    (f : X ⟶ S) (f₁ : X₁ ⟶ T) (u₁ : T ⟶ S) (v : X₁ ⟶ X)
    (h : v ≫ f = f₁ ≫ u₁) (F : X.Modules) :
    (tensorPullback u₁).obj ((pushforward f).obj F) ⟶
      (pushforward f₁).obj ((tensorPullback v).obj F) :=
  ((Classical.choose (exists_tensorPullbackAdjunction u₁)).homEquiv _ _).symm
    ((pushforward f).map
      ((Classical.choose (exists_tensorPullbackAdjunction v)).unit.app F) ≫
      (pushforwardComp v f).hom.app ((tensorPullback v).obj F) ≫
      (pushforwardCongr h).hom.app ((tensorPullback v).obj F) ≫
      (pushforwardComp f₁ u₁).inv.app ((tensorPullback v).obj F))

private noncomputable abbrev adj {A B : Scheme.{u}} (k : A ⟶ B) :=
  Classical.choose (exists_tensorPullbackAdjunction k)

private noncomputable def pushforwardSquare {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hsq : g' ≫ f = f' ≫ g) :
    TwoSquare (pushforward g') (pushforward f') (pushforward f) (pushforward g) :=
  TwoSquare.mk _ _ _ _
    ((pushforwardComp g' f).hom ≫ (pushforwardCongr hsq).hom ≫
      (pushforwardComp f' g).inv)

private noncomputable def baseChangeSquare {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hsq : g' ≫ f = f' ≫ g) :
    TwoSquare (pushforward f) (tensorPullback g') (tensorPullback g) (pushforward f') :=
  (mateEquiv (adj g') (adj g)).symm (pushforwardSquare f f' g g' hsq)

private theorem baseChangeSquare_app {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hsq : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (baseChangeSquare f f' g g' hsq).app F = baseChangeMapCore f f' g g' hsq F := by
  apply ((adj g).homEquiv _ _).injective
  dsimp only [adj, Functor.comp_obj]
  rw [baseChangeMapCore, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (adj g') (adj g)
    (pushforwardSquare f f' g g' hsq) F).symm

private theorem baseChangeMapCore_pasting
    {X S X' S' X'' S'' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : S'' ⟶ S') (h' : X'' ⟶ X')
    (hsq₁ : g' ≫ f = f' ≫ g) (hsq₂ : h' ≫ f' = f'' ≫ h) (F : X.Modules) :
    baseChangeMapCore f f'' (h ≫ g) (h' ≫ g')
        ((Category.assoc h' g' f).trans
          ((congrArg (fun k ↦ h' ≫ k) hsq₁).trans
            ((Category.assoc h' f' g).symm.trans
              ((congrArg (fun k ↦ k ≫ g) hsq₂).trans (Category.assoc f'' h g))))) F =
      ((conjugateIsoEquiv
          ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
            (Classical.choose (exists_tensorPullbackAdjunction h)))
          (Classical.choose (exists_tensorPullbackAdjunction (h ≫ g)))).symm
          (pushforwardComp h g)).hom.app ((pushforward f).obj F) ≫
        (tensorPullback h).map (baseChangeMapCore f f' g g' hsq₁ F) ≫
        baseChangeMapCore f' f'' h h' hsq₂ ((tensorPullback g').obj F) ≫
        (pushforward f'').map
          (((conjugateIsoEquiv
            ((Classical.choose (exists_tensorPullbackAdjunction g')).comp
              (Classical.choose (exists_tensorPullbackAdjunction h')))
            (Classical.choose (exists_tensorPullbackAdjunction (h' ≫ g')))).symm
            (pushforwardComp h' g')).inv.app F) := by
  let c := (conjugateIsoEquiv ((adj g).comp (adj h)) (adj (h ≫ g))).symm
    (pushforwardComp h g)
  let c' := (conjugateIsoEquiv ((adj g').comp (adj h')) (adj (h' ≫ g'))).symm
    (pushforwardComp h' g')
  let hsq := (Category.assoc h' g' f).trans
    ((congrArg (fun k ↦ h' ≫ k) hsq₁).trans
      ((Category.assoc h' f' g).symm.trans
        ((congrArg (fun k ↦ k ≫ g) hsq₂).trans (Category.assoc f'' h g))))
  have hc : conjugateEquiv ((adj g).comp (adj h)) (adj (h ≫ g)) c.hom =
      (pushforwardComp h g).hom := by
    simp [c]
  have hc' : conjugateEquiv (adj (h' ≫ g')) ((adj g').comp (adj h')) c'.inv =
      (pushforwardComp h' g').inv := by
    simp [c']
  have key : baseChangeSquare f f'' (h ≫ g) (h' ≫ g') hsq =
      ((TwoSquare.vComp (baseChangeSquare f f' g g' hsq₁)
        (baseChangeSquare f' f'' h h' hsq₂)).whiskerLeft c'.inv).whiskerRight c.hom := by
    apply (mateEquiv (adj (h' ≫ g')) (adj (h ≫ g))).injective
    rw [mateEquiv_conjugateEquiv_vcomp _ ((adj g).comp (adj h)),
      conjugateEquiv_mateEquiv_vcomp _ ((adj g').comp (adj h')),
      mateEquiv_hcomp, hc, hc']
    simp only [baseChangeSquare, Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext M
    apply hom_ext
    intro U
    simp only [pushforwardSquare, TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Hom.comp_app, pushforward_map_app,
      pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id]
    change M.presheaf.map _ = M.presheaf.map _ ≫ M.presheaf.map _
    rw [← Functor.map_comp]
    congr 1
  have keyF := congrArg (fun w ↦ w.app F) key
  simpa [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    baseChangeSquare_app, c, c'] using keyF


private theorem baseChangeMapCore_congr {X S T Y : Scheme.{u}}
    (f : X ⟶ S) (q : Y ⟶ T) (r r' : T ⟶ S) (s s' : Y ⟶ X)
    (h : s ≫ f = q ≫ r) (h' : s' ≫ f = q ≫ r')
    (er : r = r') (es : s = s') (F : X.Modules) :
    (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj ((pushforward f).obj F)) er)).hom ≫
        baseChangeMapCore f q r' s' h' F =
      baseChangeMapCore f q r s h F ≫
        (pushforward q).map
          (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F) es)).hom := by
  cases er
  cases es
  simp

/-- Base change commutes with restriction of a commutative square. This is purely
pasting coherence: the four vertical maps need not be open immersions.
Source: Stacks Project, Cohomology, Remarks 0ATL and 0ATM, with Remark 08HY.
(blueprint: lem-weil-pbc-module-square-restriction-commutes)

Proof: paste the original square with the primed restriction square. Taking mates
of the sectionwise pushforward composition identity gives the outer base change map
as c(jV,g).hom followed by jV* beta, rho' and the inverse top composition comparison.
Paste instead the unprimed restriction square with the smaller square. The same mate
identity gives c(gV,jU).hom followed by gV* rho, betaV and the other inverse top
comparison. The outer bottom and top maps are equal by hg and hg'; transport the
second equality along these equalities. Naturality of equality transport and
cancellation of the composition isomorphisms give precisely the displayed equality.
The mate identity follows from mateEquiv_hcomp and the compatibility of mateEquiv
with conjugateEquiv; the pushforward identity holds sectionwise by functoriality of
presheaf restriction. No inverse-image or openness assumptions enter this argument. -/
theorem moduleBaseChangeMap_square_restriction_commutes
    {X S X' S' U V XU X'V : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (jU : U ⟶ S) (jV : V ⟶ S') (jX : XU ⟶ X) (jX' : X'V ⟶ X')
    (fU : XU ⟶ U) (fV' : X'V ⟶ V) (gV : V ⟶ U) (gV' : X'V ⟶ XU)
    (hf : jX ≫ f = fU ≫ jU) (hf' : jX' ≫ f' = fV' ≫ jV)
    (hg : jV ≫ g = gV ≫ jU) (hg' : jX' ≫ g' = gV' ≫ jX)
    (hV : gV' ≫ fU = fV' ≫ gV)
    :
    let bc : ∀ {A B C D : Scheme.{u}} (p : A ⟶ B) (q : C ⟶ D)
        (r : D ⟶ B) (s : C ⟶ A) (_hs : s ≫ p = q ≫ r) (M : A.Modules),
        (tensorPullback r).obj ((pushforward p).obj M) ⟶
          (pushforward q).obj ((tensorPullback s).obj M) :=
      fun {_A _B _C _D : Scheme.{u}} p q r s hs M ↦
        ((Classical.choose (exists_tensorPullbackAdjunction r)).homEquiv _ _).symm
          ((pushforward p).map
            ((Classical.choose (exists_tensorPullbackAdjunction s)).unit.app M) ≫
            (pushforwardComp s p).hom.app ((tensorPullback s).obj M) ≫
            (pushforwardCongr hs).hom.app ((tensorPullback s).obj M) ≫
            (pushforwardComp q r).inv.app ((tensorPullback s).obj M))
    let adj : ∀ {A B : Scheme.{u}} (k : A ⟶ B), tensorPullback k ⊣ pushforward k :=
      fun {A B : Scheme.{u}} (k : A ⟶ B) ↦
      Classical.choose (exists_tensorPullbackAdjunction k)
    let c : ∀ {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C),
        tensorPullback (k ≫ l) ≅ tensorPullback l ⋙ tensorPullback k :=
      fun {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C) ↦
      (conjugateIsoEquiv ((adj l).comp (adj k)) (adj (k ≫ l))).symm
        (pushforwardComp k l)
    let rho := fun F : X.Modules ↦ bc f fU jU jX hf F
    let rho' := fun G : X'.Modules ↦ bc f' fV' jV jX' hf' G
    ∀ F : X.Modules,
      let a := (c jV g).inv.app ((pushforward f).obj F) ≫
        (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj ((pushforward f).obj F)) hg)).hom ≫
        (c gV jU).hom.app ((pushforward f).obj F) ≫ (tensorPullback gV).map (rho F)
      let b := rho' ((tensorPullback g').obj F) ≫
        (pushforward fV').map ((c jX' g').inv.app F) ≫
        (pushforward fV').map
          (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F) hg')).hom ≫
        (pushforward fV').map ((c gV' jX).hom.app F)
      let beta := bc f f' g g' h F
      let betaV := bc fU fV' gV gV' hV ((tensorPullback jX).obj F)
      (tensorPullback jV).map beta ≫ b = a ≫ betaV := by
  intro bc adj c rho rho' F a b beta betaV
  have ho₁ : (jX' ≫ g') ≫ f = fV' ≫ (jV ≫ g) := by
    rw [Category.assoc, h, ← Category.assoc, hf', Category.assoc]
  have ho₂ : (gV' ≫ jX) ≫ f = fV' ≫ (gV ≫ jU) := by
    rw [Category.assoc, hf, ← Category.assoc, hV, Category.assoc]
  have h₁ : baseChangeMapCore f fV' (jV ≫ g) (jX' ≫ g') ho₁ F =
      (c jV g).hom.app ((pushforward f).obj F) ≫
        (tensorPullback jV).map beta ≫ rho' ((tensorPullback g').obj F) ≫
        (pushforward fV').map ((c jX' g').inv.app F) :=
    baseChangeMapCore_pasting f f' fV' g g' jV jX' h hf' F
  have h₂ : baseChangeMapCore f fV' (gV ≫ jU) (gV' ≫ jX) ho₂ F =
      (c gV jU).hom.app ((pushforward f).obj F) ≫
        (tensorPullback gV).map (rho F) ≫ betaV ≫
        (pushforward fV').map ((c gV' jX).inv.app F) :=
    baseChangeMapCore_pasting f fU fV' jU jX gV gV' hf hV F
  have ht := baseChangeMapCore_congr f fV' (jV ≫ g) (gV ≫ jU)
    (jX' ≫ g') (gV' ≫ jX) ho₁ ho₂ hg hg' F
  apply (cancel_epi ((c jV g).hom.app ((pushforward f).obj F))).mp
  apply (cancel_mono ((pushforward fV').map ((c gV' jX).inv.app F))).mp
  dsimp only [a, b]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Category.comp_id, Iso.hom_inv_id_app_assoc]
  simpa only [h₁, h₂, Functor.map_comp, Category.assoc] using ht.symm

end
end AlgebraicGeometry.Scheme.Modules
