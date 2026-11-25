/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarOrdinaryInterface
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows

/-! # Canonical normalization of the ordinary scalar alpha

Source: Stacks, Tags 03D7, 03DI and 0F7B; the intrinsic proper/open word.
(blueprint: lem-sf-semilinear-scalar-ordinary-alpha-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable {R : ℕ → CommRingCat.{u + 1}} {φ : ∀ n : ℕ, R (n + 1) ⟶ R n}
  {B : Type (u + 1)} [CommRing B] {ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n}

attribute [local irreducible] Functor.leftAdjoint StrictTower.modulePullback
attribute [local irreducible] StrictTower.moduleJAdj
attribute [local irreducible] StrictTower.openBetaModule StrictTower.openBetaModuleJComp
attribute [local irreducible] StrictTower.clopenModulePi StrictTower.singleJCongr

private theorem unit_normalized_map
    {C D : Type*} [Category C] [Category D]
    {L : D ⥤ C} {G : C ⥤ D} {P : D ⥤ C}
    (a : L ⊣ G) (b : G ⊣ P) [IsIso a.unit] (N : D)
    (t : L.obj N ⟶ P.obj N)
    (ht : a.unit.app N ≫ (b.homEquiv _ _).symm t = 𝟙 N) :
    t = b.unit.app (L.obj N) ≫ P.map ((inv a.unit).app N) := by
  have hh : (b.homEquiv _ _).symm t = (inv a.unit).app N := by
    apply (cancel_epi (a.unit.app N)).1
    rw [ht]
    simp only [NatIso.isIso_inv_app, IsIso.hom_inv_id]
    rfl
  calc
    t = b.homEquiv _ _ ((b.homEquiv _ _).symm t) :=
      ((b.homEquiv _ _).apply_symm_apply t).symm
    _ = _ := by rw [hh]; rfl

private theorem towerSquare_inv_app
    {C A A' E : Type*} [Category C] [Category A] [Category A'] [Category E]
    (F₁ : C ⥤ A) (F₂ : A ⥤ E) (G₁ : C ⥤ A') (G₂ : A' ⥤ E)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (M : ℕᵒᵖ ⥤ C) (n : ℕᵒᵖ) :
    ((StrictTower.towerSquare F₁ F₂ G₁ G₂ e).inv.app M).app n =
      e.inv.app (M.obj n) := by
  rw [StrictTower.towerSquare_eq]
  rfl

private theorem towerSquare_inv_app_of_eq
    {C A A' E : Type*} [Category C] [Category A] [Category A'] [Category E]
    (F₁ : C ⥤ A) (F₂ : A ⥤ E) (G₁ : C ⥤ A') (G₂ : A' ⥤ E)
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (q : (Functor.whiskeringRight ℕᵒᵖ C A).obj F₁ ⋙
        (Functor.whiskeringRight ℕᵒᵖ A E).obj F₂ ≅
      (Functor.whiskeringRight ℕᵒᵖ C A').obj G₁ ⋙
        (Functor.whiskeringRight ℕᵒᵖ A' E).obj G₂)
    (he : q = StrictTower.towerSquare F₁ F₂ G₁ G₂ e)
    (M : ℕᵒᵖ ⥤ C) (n : ℕᵒᵖ) :
    (q.inv.app M).app n = e.inv.app (M.obj n) := by
  subst q
  exact towerSquare_inv_app _ _ _ _ _ M n

private theorem square_inv_app {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (h : k ≫ p = r ≫ i) (M : StrictTower.Towers B T) (n : ℕᵒᵖ) :
    ((scalarTowerSquare B k r p i h).inv.app M).app n =
    (StrictTower.moduleSquareG B k r p i h).inv.app (M.obj n) := by
  exact towerSquare_inv_app_of_eq
    (StrictTower.modulePullback B i) (StrictTower.modulePullback B r)
    (StrictTower.modulePullback B p) (StrictTower.modulePullback B k)
    (StrictTower.moduleSquareG B k r p i h) (scalarTowerSquare B k r p i h)
    (StrictTower.towerSquare_moduleSquareG.{u} B k r p i h).symm M n

private theorem beta_inv_app (D : OrdinaryScalarComparison R φ B ψ)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (hsq : IsPullback a j' j g)
    (M : StrictTower.Towers B U) (n : ℕᵒᵖ) :
    ((D.beta a j' j g h hsq).inv.app M).app n =
      (StrictTower.openBetaModule B a j' j g h hsq).inv.app (M.obj n) := by
  apply ((StrictTower.moduleJAdj.{u} B j').homEquiv
    ((StrictTower.modulePullback B a).obj (M.obj n))
    ((StrictTower.modulePullback B g).obj ((StrictTower.moduleJ B j).obj (M.obj n)))).injective
  have hd := congrArg (fun f ↦ f.app n) (D.beta_unit a j' j g h hsq M)
  have hn := (StrictTower.openBetaModule_normalized.{u} B a j' j g h hsq).2 (M.obj n)
  simp only [Adjunction.homEquiv_unit, scalarTowerOpenAdj, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app, square_inv_app,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app] at hd
  simp only [Adjunction.homEquiv_unit] at hn
  dsimp only [StrictTower.towerJ, StrictTower.towerPullback, Functor.whiskeringRight,
    Functor.comp_obj] at hd
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact hd.trans hn.symm

private theorem clopen_hom_app (D : OrdinaryScalarComparison R φ B ψ)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (N : StrictTower.Towers B U) (n : ℕᵒᵖ) :
    ((D.clopen s).hom.app N).app n =
      (StrictTower.clopenModuleToDirect.{u} B s).app (N.obj n) := by
  have : IsIso (StrictTower.moduleJAdj.{u} B s).unit :=
    StrictTower.clopenModule_openUnit_isIso.{u} B s
  have hd := congrArg (fun f ↦ f.app n) (D.clopen_unit s N)
  simp only [scalarTowerOpenAdj, scalarTowerAdj,
    NatTrans.comp_app, Adjunction.whiskerRight_unit_app_app] at hd
  have ht := unit_normalized_map (StrictTower.moduleJAdj.{u} B s)
    (StrictTower.clopenModuleAdj.{u} B s) (N.obj n) (((D.clopen s).hom.app N).app n) hd
  change ((D.clopen s).hom.app N).app n = _
  simpa only [StrictTower.clopenModuleToDirect, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Functor.id_obj] using ht

private theorem beta_hom_app (D : OrdinaryScalarComparison R φ B ψ)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (hsq : IsPullback a j' j g)
    (M : StrictTower.Towers B U) (n : ℕᵒᵖ) :
    ((D.beta a j' j g h hsq).hom.app M).app n =
      (StrictTower.openBetaModule B a j' j g h hsq).hom.app (M.obj n) := by
  apply (cancel_mono ((StrictTower.openBetaModule B a j' j g h hsq).inv.app
    (M.obj n))).1
  have hi := congrArg (fun f ↦ f.app n) ((D.beta a j' j g h hsq).hom_inv_id_app M)
  change ((D.beta a j' j g h hsq).hom.app M).app n ≫
    ((D.beta a j' j g h hsq).inv.app M).app n = 𝟙 _ at hi
  rw [beta_inv_app D a j' j g h hsq M n] at hi
  exact hi.trans ((StrictTower.openBetaModule B a j' j g h hsq).hom_inv_id_app
    (M.obj n)).symm

private theorem pi_app (D : OrdinaryScalarComparison R φ B ψ)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (M : StrictTower.Towers B X) (n : ℕᵒᵖ) :
    ((D.pi s).app M).app n = (StrictTower.clopenModulePi B s).app (M.obj n) := by
  have ht := StrictTower.clopenModuleToDirect_isIso.{u} B s
  rw [D.pi_eq]
  change ((scalarTowerAdj B s).unit.app M).app n ≫
    ((D.clopen s).inv.app _).app n = _
  have hc : ((D.clopen s).inv.app ((StrictTower.towerPullback B s).obj M)).app n =
      (inv (StrictTower.clopenModuleToDirect B s)).app
        ((StrictTower.modulePullback B s).obj (M.obj n)) := by
    apply (cancel_mono ((StrictTower.clopenModuleToDirect B s).app _)).1
    have hi := congrArg (fun f ↦ f.app n)
      ((D.clopen s).inv_hom_id_app ((StrictTower.towerPullback B s).obj M))
    change ((D.clopen s).inv.app _).app n ≫ ((D.clopen s).hom.app _).app n = 𝟙 _ at hi
    rw [clopen_hom_app D s _ n] at hi
    exact hi.trans ((asIso (StrictTower.clopenModuleToDirect B s)).inv_hom_id_app
      ((StrictTower.modulePullback B s).obj (M.obj n))).symm
  rw [hc]
  unfold StrictTower.clopenModulePi
  rfl

private abbrev tw {A C : Type*} [Category A] [Category C] (f : A ⥤ C) :
    (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ C) := (Functor.whiskeringRight ℕᵒᵖ A C).obj f

private theorem framed_app
    {A C E F : Type*} [Category A] [Category C] [Category E] [Category F]
    (f : A ⥤ C) (g : C ⥤ F) (h : A ⥤ E) (k : E ⥤ F)
    (t : f ⋙ g ⟶ h ⋙ k) (M : ℕᵒᵖ ⥤ A) (n : ℕᵒᵖ) :
    ((Functor.termwiseCompositeTransformation ℕᵒᵖ A C E F f g h k t).app M).app n =
      t.app (M.obj n) := by
  simp only [Functor.termwiseCompositeTransformation, Functor.whiskeringRightObjCompIso,
    Functor.whiskeringRight, Functor.comp_obj, Iso.refl_hom, Iso.refl_inv,
    NatTrans.comp_app, NatTrans.id_app, Category.id_comp, Category.comp_id]

private theorem beta_eq_framed (D : OrdinaryScalarComparison R φ B ψ)
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : a ≫ j = j' ≫ g) (hsq : IsPullback a j' j g) :
    (D.beta a j' j g h hsq).hom = Functor.termwiseCompositeTransformation ℕᵒᵖ
      (StrictTower.Modules B U) (StrictTower.Modules B X)
      (StrictTower.Modules B U') (StrictTower.Modules B X')
      (StrictTower.moduleJ B j) (StrictTower.modulePullback B g)
      (StrictTower.modulePullback B a) (StrictTower.moduleJ B j')
      (StrictTower.openBetaModule B a j' j g h hsq).hom := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  rw [framed_app]
  exact beta_hom_app D a j' j g h hsq M n

private theorem pi_eq_canonical (D : OrdinaryScalarComparison R φ B ψ)
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    D.pi s = StrictTower.clopenTowerPi B s := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  exact pi_app D s M n

private theorem openTail_eq {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    (l : U ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
    (h : j ≫ k = l) :
    (scalarTowerOpenComp B j k).hom ≫ (eqToIso (scalarTowerOpen_congr B h)).hom =
      StrictTower.towerJTail B j k l h := by
  subst l
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, StrictTower.towerJTail,
    StrictTower.singleJCongr_refl]
  have ht := StrictTower.whisker_comp_hom (StrictTower.moduleJAdj.{u} B j)
    (StrictTower.moduleJAdj.{u} B k) (StrictTower.moduleJAdj.{u} B (j ≫ k))
    (StrictTower.moduleGComp B j k)
  simpa only [scalarTowerOpenComp, scalarTowerOpenAdj, StrictTower.towerGComp,
    StrictTower.openBetaModuleJComp, StrictTower.termwiseCompHom,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using ht

private theorem pullTail_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : X ⟶ Z) (h : f ≫ g = r) :
    (StrictTower.towerGComp B f g).inv ≫
        (eqToIso (congrArg (StrictTower.towerPullback B) h)).hom =
      StrictTower.towerGTail B f g r h := by
  subst r
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, StrictTower.towerGTail,
    StrictTower.termwiseCompHom, StrictTower.towerGComp, Iso.trans_inv,
    Functor.mapIso_inv]

private def word4
    {A T P V W : Type*} [Category A] [Category T] [Category P]
    [Category V] [Category W]
    (f : A ⥤ T) (g : T ⥤ W) (q : A ⥤ P) (s : P ⥤ V)
    (j : V ⥤ P) (b : P ⥤ W) (k : V ⥤ W) (r : A ⥤ V)
    (β : f ⋙ g ⟶ q ⋙ b) (π : 𝟭 P ⟶ s ⋙ j)
    (a : j ⋙ b ⟶ k) (e : q ⋙ s ⟶ r) : f ⋙ g ⟶ r ⋙ k :=
  β ≫ Functor.whiskerRight (Functor.whiskerLeft q π) b ≫
    Functor.whiskerLeft (q ⋙ s) a ≫ Functor.whiskerRight e k

private theorem word4_congr
    {A T P V W : Type*} [Category A] [Category T] [Category P]
    [Category V] [Category W]
    (f : A ⥤ T) (g : T ⥤ W) (q : A ⥤ P) (s : P ⥤ V)
    (j : V ⥤ P) (b : P ⥤ W) (k : V ⥤ W) (r : A ⥤ V)
    {β β' : f ⋙ g ⟶ q ⋙ b} {π π' : 𝟭 P ⟶ s ⋙ j}
    {a a' : j ⋙ b ⟶ k} {e e' : q ⋙ s ⟶ r}
    (hβ : β = β') (hπ : π = π') (ha : a = a') (he : e = e') :
    word4 f g q s j b k r β π a e = word4 f g q s j b k r β' π' a' e' := by
  subst β' π' a' e'
  rfl

private theorem eq_word4
    {A T P V W : Type*} [Category A] [Category T] [Category P]
    [Category V] [Category W]
    (f : A ⥤ T) (g : T ⥤ W) (q : A ⥤ P) (s : P ⥤ V)
    (j : V ⥤ P) (b : P ⥤ W) (l k : V ⥤ W) (t r : A ⥤ V)
    (β : f ⋙ g ⟶ q ⋙ b) (π : 𝟭 P ⟶ s ⋙ j)
    (a : j ⋙ b ⟶ l) (c : l ⟶ k) (e : q ⋙ s ⟶ t) (d : t ⟶ r)
    (α : f ⋙ g ⟶ r ⋙ k)
    (hα : ∀ M, α.app M = β.app M ≫ b.map (π.app (q.obj M)) ≫
      a.app (s.obj (q.obj M)) ≫ c.app (s.obj (q.obj M)) ≫
        k.map (e.app M ≫ d.app M)) :
    α = word4 f g q s j b k r β π (a ≫ c) (e ≫ d) := by
  apply NatTrans.ext
  funext M
  simpa only [word4, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc] using hα M

private theorem termwise_word4
    {A T P V W : Type*} [Category A] [Category T] [Category P]
    [Category V] [Category W]
    (f : A ⥤ T) (g : T ⥤ W) (q : A ⥤ P) (s : P ⥤ V)
    (j : V ⥤ P) (b : P ⥤ W) (k : V ⥤ W) (r : A ⥤ V)
    (β : f ⋙ g ⟶ q ⋙ b) (π : 𝟭 P ⟶ s ⋙ j)
    (a : j ⋙ b ⟶ k) (e : q ⋙ s ⟶ r) :
    Functor.termwiseCompositeTransformation ℕᵒᵖ A T V W f g r k
        (word4 f g q s j b k r β π a e) =
      word4 (tw f) (tw g) (tw q) (tw s) (tw j) (tw b) (tw k) (tw r)
        (Functor.termwiseCompositeTransformation ℕᵒᵖ A T P W f g q b β)
        ((Functor.whiskeringRight ℕᵒᵖ P P).map π)
        (StrictTower.termwiseCompHom j b k a) (StrictTower.termwiseCompHom q s r e) := by
  unfold Functor.termwiseCompositeTransformation word4 StrictTower.termwiseCompHom
  exact StrictTower.whisker_paste f g q s j b k r β π a e

private theorem alpha_eq_word4 (D : OrdinaryScalarComparison R φ B ψ)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    D.alpha k r p i h = word4
    (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
    (StrictTower.towerPullback B (pullback.snd p i))
    (StrictTower.towerPullback B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (pullback.fst p i))
    (StrictTower.towerJ B k)
    (StrictTower.towerPullback B r)
    (D.beta (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    (D.pi (StrictTower.squareLift k r p i h))
    ((scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom)
    ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom) := by
  exact eq_word4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (D.alpha k r p i h) (D.alpha_eq k r p i h)

private theorem towerAlpha_eq_word4
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    StrictTower.towerAlpha B k r p i h = word4
    (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
    (StrictTower.towerPullback B (pullback.snd p i))
    (StrictTower.towerPullback B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (pullback.fst p i))
    (StrictTower.towerJ B k)
    (StrictTower.towerPullback B r)
    (Functor.termwiseCompositeTransformation ℕᵒᵖ
      (StrictTower.Modules B S) (StrictTower.Modules B T)
      (StrictTower.Modules B (pullback p i)) (StrictTower.Modules B W)
      (StrictTower.moduleJ B i) (StrictTower.modulePullback B p)
      (StrictTower.modulePullback B (pullback.snd p i))
      (StrictTower.moduleJ B (pullback.fst p i))
      (StrictTower.openBetaModule B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom)
    (StrictTower.clopenTowerPi B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJTail B (StrictTower.squareLift k r p i h) (pullback.fst p i) k
      (pullback.lift_fst k r h))
    (StrictTower.towerGTail B (StrictTower.squareLift k r p i h) (pullback.snd p i) r
      (pullback.lift_snd k r h)) := by
  unfold StrictTower.towerAlpha StrictTower.singleAlpha
  rw [StrictTower.assoc_paste]
  simp only [StrictTower.towerJTail, StrictTower.towerGTail, StrictTower.clopenTowerPi]
  exact termwise_word4 _ _ _ _ _ _ _ _ _ _ _ _

/-- The alpha of a normalized ordinary scalar package is canonical.
Source: Stacks, Tags 03D7, 03DI and 0F7B, and the intrinsic proper/open word.
(blueprint: lem-sf-semilinear-scalar-ordinary-alpha-normalization).
Proof: beta_unit identifies the inverse cartesian beta by injectivity of the open
adjunction Hom equivalence. clopen_unit identifies the open-to-direct map with the
transpose of the inverse open unit; pi_eq then identifies its projector with the
canonical clopen projector. The unit-normalized open compositor is the whiskering
of the single-level compositor. Transport along equality is checked by substitution
of the equality, where both maps are identities. Substitute these identifications
in alpha_eq. The ordinary alpha word is the termwise image of singleAlpha: whiskering
preserves composition and its compositor components are identities. This is exactly
towerAlpha, for arbitrary commutative proper/open squares. No derived evaluation or
faithfulness assertion is involved. -/
theorem scalarOrdinaryAlphaNormalization (D : OrdinaryScalarComparison R φ B ψ)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    D.alpha k r p i h = StrictTower.towerAlpha B k r p i h := by
  have he := alpha_eq_word4 D k r p i h
  have hn := word4_congr
    (StrictTower.towerJ B i) (StrictTower.towerPullback B p)
    (StrictTower.towerPullback B (pullback.snd p i))
    (StrictTower.towerPullback B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (StrictTower.squareLift k r p i h))
    (StrictTower.towerJ B (pullback.fst p i))
    (StrictTower.towerJ B k) (StrictTower.towerPullback B r)
    (beta_eq_framed D (pullback.snd p i) (pullback.fst p i) i p
      pullback.condition.symm (IsPullback.of_hasPullback p i).flip)
    (pi_eq_canonical D (StrictTower.squareLift k r p i h))
    (openTail_eq (B := B) (StrictTower.squareLift k r p i h) (pullback.fst p i) k
      (pullback.lift_fst k r h))
    (pullTail_eq (B := B) (StrictTower.squareLift k r p i h) (pullback.snd p i) r
      (pullback.lift_snd k r h))
  exact he.trans (hn.trans (towerAlpha_eq_word4 (B := B) k r p i h).symm)

end AlgebraicGeometry.ProEtale.VaryingRing
