/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionMaps
import all WeilConjectures.AlgebraicGeometry.StrictTower.RefinementExchangeCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization

/-!
# Composition pasting for strict constant-coefficient towers

Source: Stacks Project, Tags 0F7J, 0F7C, 0F7D and 0F7F.
The shared constructions live in `StrictTowerCompositionMaps`, so refinement
independence can be used here without an import cycle.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

-- Prove pasting with abstract functors, then identify its factors with the library maps.
section PastingCalculation

attribute [local irreducible] G R J adj rComp jComp rId jCongr jAdj gamma beta exchange
  gComp gId squareG
private theorem conjugate_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    conjugateIsoEquiv (adj B f) (adj B g) (eqToIso (congrArg (G B) e.symm)) =
      eqToIso (congrArg (R B) e) := by
  cases e
  apply Iso.ext
  exact conjugateEquiv_id _

private noncomputable def pComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (e : f ≫ g = fg) :
    R B f ⋙ R B g ≅ R B fg := rCompEq B f g fg e

private theorem pAssoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : Derived B X) :
    (R B h).map ((pComp B f g fg hfg).hom.app M) ≫
        (pComp B fg h fgh hl).hom.app M =
      (pComp B g h gh hgh).hom.app ((R B f).obj M) ≫
        (pComp B f gh fgh hr).hom.app M :=
  (strictTowerDirectImageCoherence B).2.1 f g h fg gh fgh hfg hgh hl hr M

private noncomputable def jCompNamed {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    (e : f ≫ g = fg) : J B f ⋙ J B g ≅ J B fg :=
  jComp B f g ≪≫ jCongr B e

private theorem rComp_id_right {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived B X) :
    (rComp B f (𝟙 Y) ≪≫ eqToIso (congrArg (R B) (Category.comp_id f))).hom.app M =
      (rId B Y).hom.app ((R B f).obj M) := by
  have hg : gComp B f (𝟙 Y) ≪≫ Functor.isoWhiskerRight (gId B Y) (G B f) ≪≫
      Functor.leftUnitor (G B f) =
      eqToIso (congrArg (G B) (Category.comp_id f)) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.id_obj]
    calc
      _ = (gComp B f (𝟙 Y)).hom.app M ≫
          (G B f).map ((gId B Y).hom.app M) :=
        congrArg (fun t ↦ (gComp B f (𝟙 Y)).hom.app M ≫ t)
          (Category.comp_id ((G B f).map ((gId B Y).hom.app M)))
      _ = _ := congr_app (gComp_id_right B f) M
  have hr := congrArg (conjugateIsoEquiv (adj B f) (adj B (f ≫ 𝟙 Y))) hg
  rw [conjugateIsoEquiv_trans _ ((adj B (𝟙 Y)).comp (adj B f)) _] at hr
  rw [conjugateIsoEquiv_trans _ (Adjunction.id.comp (adj B f)) _] at hr
  simp only [conjugateIsoEquiv_leftUnitor,
    conjugateIsoEquiv_isoWhiskerRight] at hr
  simp only [Iso.trans_assoc] at hr
  have hid : conjugateIsoEquiv Adjunction.id (adj B (𝟙 Y)) (gId B Y) =
      (rId B Y).symm := by
    unfold rId
    rfl
  rw [hid] at hr
  have hcomp : conjugateIsoEquiv ((adj B (𝟙 Y)).comp (adj B f))
      (adj B (f ≫ 𝟙 Y)) (gComp B f (𝟙 Y)) = rComp B f (𝟙 Y) := by
    unfold rComp
    rfl
  rw [hcomp] at hr
  rw [conjugate_transport B (Category.comp_id f).symm] at hr
  have hM := congrArg (fun e ↦ e.hom.app M) hr
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.id_comp] at hM
  apply (cancel_epi ((rId B Y).inv.app ((R B f).obj M))).1
  simp only [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc, hM]
  simp only [Iso.inv_hom_id_app]
  change (eqToIso (congrArg (R B) (Category.comp_id f))).inv.app M ≫
    (eqToIso (congrArg (R B) (Category.comp_id f))).hom.app M = _
  exact (eqToIso (congrArg (R B) (Category.comp_id f))).inv_hom_id_app M

private theorem pRight {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Derived B X) :
    (pComp B f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (rId B Y).hom.app ((R B f).obj M) := by
  rw [pComp, rCompEq_eq]
  exact rComp_id_right B f M

private theorem cancel_pasting_app {A C D E F H : Type*}
    [Category A] [Category C] [Category D] [Category E] [Category F] [Category H]
    (P : A ⥤ C) (Q : C ⥤ D) (R : A ⥤ D)
    (P' : E ⥤ F) (Q' : F ⥤ H) (R' : E ⥤ H)
    (Gt : A ⥤ E) (Gh : C ⥤ F) (Gb : D ⥤ H)
    (a₀ : R ⋙ Gb ⟶ Gt ⋙ R') (a₁ : Q ⋙ Gb ⟶ Gh ⋙ Q')
    (a₂ : P ⋙ Gh ⟶ Gt ⋙ P') (c₀ : P ⋙ Q ≅ R) (c₁ : P' ⋙ Q' ≅ R')
    (M : A)
    (he : Gb.map (c₀.hom.app M) ≫ a₀.app M =
      a₁.app (P.obj M) ≫ Q'.map (a₂.app M) ≫ c₁.hom.app (Gt.obj M)) :
    a₀.app M = Gb.map (c₀.inv.app M) ≫ a₁.app (P.obj M) ≫
      Q'.map (a₂.app M) ≫ c₁.hom.app (Gt.obj M) := by
  apply (cancel_epi (Gb.map (c₀.hom.app M))).1
  simpa only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] using he

private theorem proper_pasting {U' U W' W Z' Z : Scheme.{u}}
    (t : U' ⟶ U) (h : W' ⟶ W) (b : Z' ⟶ Z)
    (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z)
    (l : U' ⟶ Z') (r : U ⟶ Z)
    (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b)
    (hl : l₁ ≫ l₂ = l) (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b)
    (M : Derived B U) :
    (refinementExchange B t l r b w).app M =
      (G B b).map ((pComp B r₁ r₂ r hr).inv.app M) ≫
        (refinementExchange B h l₂ r₂ b w₂).app ((R B r₁).obj M) ≫
        (R B l₂).map ((refinementExchange B t l₁ r₁ h w₁).app M) ≫
        (pComp B l₁ l₂ l hl).hom.app ((G B t).obj M) := by
  exact cancel_pasting_app (R B r₁) (R B r₂) (R B r)
    (R B l₁) (R B l₂) (R B l) (G B t) (G B h) (G B b)
    (refinementExchange B t l r b w) (refinementExchange B h l₂ r₂ b w₂)
    (refinementExchange B t l₁ r₁ h w₁) (pComp B r₁ r₂ r hr) (pComp B l₁ l₂ l hl) M
    (refinementMatePasting B U W Z U' W' Z' r₁ r₂ r l₁ l₂ l t h b hr hl w₁ w₂ w M)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- The category and scheme universes meet in the functor categories used by this record.
set_option linter.checkUnivs false in
private structure RawPastingData where
  obj : Scheme.{u} → Type w
  [category (X : Scheme.{u}) : Category.{v} (obj X)]
  R {X Y : Scheme.{u}} (f : X ⟶ Y) : obj X ⥤ obj Y
  G {X Y : Scheme.{u}} (f : X ⟶ Y) : obj Y ⥤ obj X
  J {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] : obj X ⥤ obj Y
  rId (X : Scheme.{u}) : R (𝟙 X) ≅ 𝟭 (obj X)
  pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (e : f ≫ g = fg) : R f ⋙ R g ≅ R fg
  jCompNamed {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    (e : f ≫ g = fg) : J f ⋙ J g ≅ J fg
  gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : R r ⋙ J i ⟶ J k ⋙ R p
  beta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : J j ⋙ G g ≅ G gU ⋙ J j'
  exchange {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    R p ⋙ G i ⟶ G k ⋙ R r
  pAssoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : obj X) :
    (R h).map ((pComp f g fg hfg).hom.app M) ≫
        (pComp fg h fgh hl).hom.app M =
      (pComp g h gh hgh).hom.app ((R f).obj M) ≫
        (pComp f gh fgh hr).hom.app M
  pRight {X Y : Scheme.{u}} (f : X ⟶ Y) (M : obj X) :
    (pComp f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (rId Y).hom.app ((R f).obj M)
  beta_open_comp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (sk : IsPullback b k₁ k a) (sj : IsPullback a j₁ j g)
    (s : IsPullback b (k₁ ≫ j₁) (k ≫ j) g) (M : obj V) :
    (G g).map ((jCompNamed k j (k ≫ j) rfl).inv.app M) ≫
        (beta a j₁ j g wj sj).hom.app ((J k).obj M) ≫
        (J j₁).map ((beta b k₁ k a wk sk).hom.app M) ≫
        (jCompNamed k₁ j₁ (k₁ ≫ j₁) rfl).hom.app ((G b).obj M) =
      (beta b (k₁ ≫ j₁) (k ≫ j) g w s).hom.app M
  calculus :
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : obj A),
      (J j).map ((pComp r₁ r₂ (r₁ ≫ r₂) rfl).hom.app M) ≫
          (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (pComp p₁ p₂ (p₁ ≫ p₂) rfl).inv.app ((J k).obj M) =
        (gamma i r₂ p₂ j h₂).app ((R r₁).obj M) ≫
          (R p₂).map ((gamma k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : obj A),
      (jCompNamed i j (i ≫ j) rfl).hom.app ((R r).obj M) ≫
          (gamma (k ≫ l) r q (i ≫ j) h).app M ≫
          (R q).map ((jCompNamed k l (k ≫ l) rfl).inv.app M) =
        (J j).map ((gamma k r p i h₁).app M) ≫
          (gamma l p q j h₂).app ((J k).obj M)) ∧
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (_sp : IsPullback a p₁ p b) (_sr : IsPullback d r₁ r c) (M : obj V),
      (G b).map ((gamma k r p i h).app M) ≫
          (exchange a p₁ p b wp).app ((J k).obj M) ≫
          (R p₁).map ((beta d k₁ k a wk sk).hom.app M) =
        (beta c i₁ i b wi si).hom.app ((R r).obj M) ≫
          (J i₁).map ((exchange d r₁ r c wr).app M) ≫
          (gamma k₁ r₁ p₁ i₁ h₁).app ((G d).obj M))
  proper_pasting {U' U W' W Z' Z : Scheme.{u}}
    (t : U' ⟶ U) (h : W' ⟶ W) (b : Z' ⟶ Z)
    (l₁ : U' ⟶ W') (r₁ : U ⟶ W) (l₂ : W' ⟶ Z') (r₂ : W ⟶ Z)
    (l : U' ⟶ Z') (r : U ⟶ Z)
    (w₁ : t ≫ r₁ = l₁ ≫ h) (w₂ : h ≫ r₂ = l₂ ≫ b)
    (hl : l₁ ≫ l₂ = l) (hr : r₁ ≫ r₂ = r) (w : t ≫ r = l ≫ b)
    (M : obj U) :
    (exchange t l r b w).app M =
      (G b).map ((pComp r₁ r₂ r hr).inv.app M) ≫
        (exchange h l₂ r₂ b w₂).app ((R r₁).obj M) ≫
        (R l₂).map ((exchange t l₁ r₁ h w₁).app M) ≫
        (pComp l₁ l₂ l hl).hom.app ((G t).obj M)

attribute [instance] RawPastingData.category
namespace RawPastingData
variable (K : RawPastingData.{u, v, w})
private noncomputable def compositionF (K : RawPastingData.{u, v, w}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : K.obj X ⥤ K.obj Y := K.J c.i ⋙ K.R c.g

private noncomputable def compositionD (K : RawPastingData.{u, v, w}) {X Y Z : Scheme.{u}} {f : X
  ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    compositionF K T.cf ⋙ compositionF K T.cg ⟶ compositionF K T.cfg :=
  Functor.whiskerLeft (K.J T.cf.i)
    (Functor.whiskerRight (K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (K.R T.cg.g)) ≫
  Functor.whiskerRight (K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom
    (K.R T.p ⋙ K.R T.cg.g) ≫
  Functor.whiskerLeft (K.J T.cfg.i) (K.pComp T.p T.cg.g T.cfg.g T.p_g).hom

private noncomputable def compositionC (K : RawPastingData.{u, v, w}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : compositionF K d ⟶ compositionF K c :=
  Functor.whiskerRight (Functor.whiskerRight (K.rId X).inv (K.J d.i) ≫
    K.gamma c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp d.i).symm))
      (K.R d.g) ≫
  Functor.whiskerLeft (K.J c.i) (K.pComp r.hom d.g c.g r.hom_g).hom

private noncomputable def compositionE (K : RawPastingData.{u, v, w}) {X Y X' Y' : Scheme.{u}} {f
  : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) :
    compositionF K c ⋙ K.G y ⟶ K.G x ⋙ compositionF K c' :=
  Functor.whiskerLeft (K.J c.i) (K.exchange s c'.g c.g y wp) ≫
  Functor.whiskerRight (K.beta x c'.i c.i s wi si).hom (K.R c'.g)

private noncomputable def compositionH (K : RawPastingData.{u, v, w}) {X Y Z : Scheme.{u}} {f : X
  ⟶ Y} {h : Y ⟶ Z}
    {T₁ T₂ : Compactification.Triangle f h}
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i]
    (r : CompositionRefinement T₁ T₂) :
    compositionF K T₂.cf ⋙ compositionF K T₂.cg ⟶
      compositionF K T₁.cf ⋙ compositionF K T₁.cg :=
  Functor.whiskerRight (compositionC K r.rf) (compositionF K T₂.cg) ≫
    Functor.whiskerLeft (compositionF K T₁.cf) (compositionC K r.rh)

private noncomputable def compositionEf (K : RawPastingData.{u, v, w}) {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE K T.cf T'.cf x y A.d A.cf_i.w A.cf_g.w A.cf_i

private noncomputable def compositionEh (K : RawPastingData.{u, v, w}) {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE K T.cg T'.cg y g A.t A.cg_i.w A.cg_g.w A.cg_i

private noncomputable def compositionEhf (K : RawPastingData.{u, v, w}) {X Y Z X' Y' Z' :
  Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :=
  compositionE K T.cfg T'.cfg x g A.s A.cfg_i.w A.cfg_g.w A.cfg_i

private noncomputable def compositionHorizontalE (K : RawPastingData.{u, v, w}) {X Y Z X' Y' Z' :
  Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    {T : Compactification.Triangle f h} {T' : Compactification.Triangle f' h'}
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    (compositionF K T.cf ⋙ compositionF K T.cg) ⋙ K.G g ⟶
      K.G x ⋙ (compositionF K T'.cf ⋙ compositionF K T'.cg) :=
  Functor.whiskerLeft (compositionF K T.cf) (compositionEh K A) ≫
  Functor.whiskerRight (compositionEf K A) (compositionF K T'.cg)

private theorem pastingD_app (K : RawPastingData.{u, v, w}) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h :
  Y ⟶ Z}
    (T : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    (M : K.obj X) :
    (compositionD K T).app M =
      (K.R T.cg.g).map ((K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm).app
        ((K.J T.cf.i).obj M)) ≫
      (K.R T.cg.g).map ((K.R T.p).map
        ((K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom.app M)) ≫
      (K.pComp T.p T.cg.g T.cfg.g T.p_g).hom.app ((K.J T.cfg.i).obj M) := by
  rfl

private theorem pastingC_app (K : RawPastingData.{u, v, w}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) (M : K.obj X) :
    (compositionC K r).app M =
      (K.R d.g).map ((K.J d.i).map ((K.rId X).inv.app M) ≫
        (K.gamma c.i (𝟙 X) r.hom d.i
        (r.i_hom.trans (Category.id_comp d.i).symm)).app M) ≫
      (K.pComp r.hom d.g c.g r.hom_g).hom.app ((K.J c.i).obj M) := by
  rfl

private theorem pastingE_app (K : RawPastingData.{u, v, w}) {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
  {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) (M : K.obj X) :
    (compositionE K c c' x y s wi wp si).app M =
      (K.exchange s c'.g c.g y wp).app ((K.J c.i).obj M) ≫
      (K.R c'.g).map ((K.beta x c'.i c.i s wi si).hom.app M) := by
  rfl

private theorem refinement_pasting (K : RawPastingData.{u, v, w}) {X Y Z : Scheme.{u}} {f : X ⟶ Y}
  {h : Y ⟶ Z}
    (T S : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.cfg.i]
    [QuasiCompact T.q]
    [QuasiCompact S.cf.i] [QuasiCompact S.cg.i] [QuasiCompact S.cfg.i]
    [QuasiCompact S.q] (r : CompositionRefinement S T) :
    compositionD K T ≫ compositionC K r.rfh =
      compositionH K r ≫ compositionD K S := by
  let U := T.cf.Z
  let V := T.cfg.Z
  let C0 := T.cg.Z
  let U' := S.cf.Z
  let V' := S.cfg.Z
  let B' := S.cg.Z
  let ga := K.gamma S.cf.i (𝟙 X) r.rf.hom T.cf.i
    (r.rf.i_hom.trans (Category.id_comp _).symm)
  let gd := K.gamma S.cg.i (𝟙 Y) r.rh.hom T.cg.i
    (r.rh.i_hom.trans (Category.id_comp _).symm)
  let ge := K.gamma S.cfg.i (𝟙 X) r.rfh.hom T.cfg.i
    (r.rfh.i_hom.trans (Category.id_comp _).symm)
  let gf := K.gamma S.q r.rf.hom r.rfh.hom T.q r.b_comm
  let gb := K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm
  let gc := K.gamma S.q S.cf.g S.p S.cg.i S.isPullback.w.symm
  let aT := K.jCompNamed T.cf.i T.q T.cfg.i T.i_q
  let ar := K.jCompNamed S.cf.i S.q S.cfg.i S.i_q
  let pt := K.pComp r.rf.hom T.cf.g S.cf.g r.rf.hom_g
  let kh := K.pComp r.rfh.hom T.p (r.rfh.hom ≫ T.p) rfl
  let kd := K.pComp S.p r.rh.hom (r.rfh.hom ≫ T.p) r.p_comm.symm
  let gg := K.gamma S.q S.cf.g (r.rfh.hom ≫ T.p) T.cg.i
    (by rw [r.p_comm, ← Category.assoc, S.isPullback.w.symm,
      Category.assoc, r.rh.i_hom])
  have hh (M : K.obj X) :
      aT.hom.app ((K.R (𝟙 X)).obj M) ≫ ge.app M ≫
        (K.R r.rfh.hom).map (ar.inv.app M) =
      (K.J T.q).map (ga.app M) ≫ gf.app ((K.J S.cf.i).obj M) := by
    have hh₀ := K.calculus.2.1 S.cf.i S.q T.cf.i T.q
      (𝟙 X) r.rf.hom r.rfh.hom
      (r.rf.i_hom.trans (Category.id_comp _).symm) r.b_comm
      (by rw [Category.assoc, r.b_comm, ← Category.assoc, r.rf.i_hom,
        Category.id_comp]) M
    have transport (i : X ⟶ V) (j : X ⟶ V')
        [IsOpenImmersion i] [QuasiCompact i] [IsOpenImmersion j] [QuasiCompact j]
        (hi : T.cf.i ≫ T.q = i) (hj : S.cf.i ≫ S.q = j) :
        (K.jCompNamed T.cf.i T.q i hi).hom.app ((K.R (𝟙 X)).obj M) ≫
          (K.gamma j (𝟙 X) r.rfh.hom i
            (by rw [← hi, ← hj, Category.assoc, r.b_comm,
              ← Category.assoc, r.rf.i_hom, Category.id_comp])).app M ≫
          (K.R r.rfh.hom).map
            ((K.jCompNamed S.cf.i S.q j hj).inv.app M) =
        (K.J T.q).map (ga.app M) ≫
          gf.app ((K.J S.cf.i).obj M) := by
      subst i
      subst j
      simpa only [ga, gf] using hh₀
    exact transport T.cfg.i S.cfg.i T.i_q S.i_q
  have hv₁ (N : K.obj U') :
      (K.J T.cg.i).map (pt.hom.app N) ≫ gg.app N ≫
        kh.inv.app ((K.J S.q).obj N) =
      gb.app ((K.R r.rf.hom).obj N) ≫
        (K.R T.p).map (gf.app N) := by
    have hv₀ := K.calculus.1 S.q T.q T.cg.i r.rf.hom T.cf.g
      r.rfh.hom T.p r.b_comm T.isPullback.w.symm
      (by rw [← Category.assoc, r.b_comm, Category.assoc,
        T.isPullback.w.symm, Category.assoc]) N
    have transport (p : U' ⟶ Y) [IsProper p] (hp : r.rf.hom ≫ T.cf.g = p) :
        (K.J T.cg.i).map ((K.pComp r.rf.hom T.cf.g p hp).hom.app N) ≫
          (K.gamma S.q p (r.rfh.hom ≫ T.p) T.cg.i
            (by rw [← hp, ← Category.assoc, r.b_comm, Category.assoc,
              T.isPullback.w.symm, Category.assoc])).app N ≫
          kh.inv.app ((K.J S.q).obj N) =
        gb.app ((K.R r.rf.hom).obj N) ≫
          (K.R T.p).map (gf.app N) := by
      subst p
      simpa only [kh, gb, gf] using hv₀
    exact transport S.cf.g r.rf.hom_g
  have hv₂ (N : K.obj U') :
      (K.J T.cg.i).map ((K.rId Y).hom.app ((K.R S.cf.g).obj N)) ≫
          gg.app N ≫ kd.inv.app ((K.J S.q).obj N) =
        gd.app ((K.R S.cf.g).obj N) ≫
          (K.R r.rh.hom).map (gc.app N) := by
    have hv₀ := K.calculus.1 S.q S.cg.i T.cg.i S.cf.g (𝟙 Y)
      S.p r.rh.hom S.isPullback.w.symm
      (r.rh.i_hom.trans (Category.id_comp _).symm)
      (by rw [← Category.assoc, S.isPullback.w.symm, Category.assoc,
        r.rh.i_hom, Category.comp_id]) N
    have transport (p : U' ⟶ Y) (q : V' ⟶ C0)
        [IsProper p] [IsProper q] (hp : S.cf.g ≫ 𝟙 Y = p)
        (hq : S.p ≫ r.rh.hom = q) :
        (K.J T.cg.i).map
            ((K.pComp S.cf.g (𝟙 Y) p hp).hom.app N) ≫
          (K.gamma S.q p q T.cg.i
            (by rw [← hp, ← hq, ← Category.assoc, S.isPullback.w.symm,
              Category.assoc, r.rh.i_hom, Category.comp_id])).app N ≫
          (K.pComp S.p r.rh.hom q hq).inv.app ((K.J S.q).obj N) =
        gd.app ((K.R S.cf.g).obj N) ≫
          (K.R r.rh.hom).map (gc.app N) := by
      subst p
      subst q
      exact hv₀
    simpa only [gg, kd, gd, gc, K.pRight] using
      transport S.cf.g (r.rfh.hom ≫ T.p) (Category.comp_id _) r.p_comm.symm
  let ta (M : K.obj X) := (K.J T.cf.i).map ((K.rId X).inv.app M) ≫ ga.app M
  let td (N : K.obj Y) := (K.J T.cg.i).map ((K.rId Y).inv.app N) ≫ gd.app N
  let te (M : K.obj X) := (K.J T.cfg.i).map ((K.rId X).inv.app M) ≫ ge.app M
  have hh' (M : K.obj X) :
      aT.hom.app M ≫ te M =
        (K.J T.q).map (ta M) ≫ gf.app ((K.J S.cf.i).obj M) ≫
          (K.R r.rfh.hom).map (ar.hom.app M) := by
    have hh₁ : aT.hom.app M ≫ te M ≫
        (K.R r.rfh.hom).map (ar.inv.app M) =
        (K.J T.q).map (ta M) ≫ gf.app ((K.J S.cf.i).obj M) := by
      dsimp only [te, ta]
      have hn := aT.hom.naturality ((K.rId X).inv.app M)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      simp only [← Category.assoc]
      rw [← hn]
      simp only [Category.assoc]
      rw [hh]
      simp only [Functor.map_comp, Category.assoc]
    apply (cancel_mono ((K.R r.rfh.hom).map (ar.inv.app M))).mp
    simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id] using hh₁
  have hv₂' (N : K.obj U') :
      gg.app N = td ((K.R S.cf.g).obj N) ≫
        (K.R r.rh.hom).map (gc.app N) ≫
          kd.hom.app ((K.J S.q).obj N) := by
    apply (cancel_epi ((K.J T.cg.i).map
      ((K.rId Y).hom.app ((K.R S.cf.g).obj N)))).mp
    apply (cancel_mono (kd.inv.app ((K.J S.q).obj N))).mp
    dsimp only [td]
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.id_obj, CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using hv₂ N
  have hv (N : K.obj U') :
      gb.app ((K.R r.rf.hom).obj N) ≫
        (K.R T.p).map (gf.app N) ≫
          kh.hom.app ((K.J S.q).obj N) =
      (K.J T.cg.i).map (pt.hom.app N) ≫ td ((K.R S.cf.g).obj N) ≫
        (K.R r.rh.hom).map (gc.app N) ≫
          kd.hom.app ((K.J S.q).obj N) := by
    rw [← hv₂']
    apply (cancel_mono (kh.inv.app ((K.J S.q).obj N))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    exact (hv₁ N).symm
  have core (M : K.obj X) :
      gb.app ((K.J T.cf.i).obj M) ≫
        (K.R T.p).map (aT.hom.app M) ≫ (K.R T.p).map (te M) ≫
          kh.hom.app ((K.J S.cfg.i).obj M) =
      (K.J T.cg.i).map ((K.R T.cf.g).map (ta M)) ≫
        (K.J T.cg.i).map (pt.hom.app ((K.J S.cf.i).obj M)) ≫
        td ((K.R S.cf.g).obj ((K.J S.cf.i).obj M)) ≫
        (K.R r.rh.hom).map (gc.app ((K.J S.cf.i).obj M)) ≫
        (K.R r.rh.hom).map ((K.R S.p).map (ar.hom.app M)) ≫
          kd.hom.app ((K.J S.cfg.i).obj M) := by
    rw [← Category.assoc ((K.R T.p).map _), ← Functor.map_comp, hh']
    simp only [Functor.map_comp, Category.assoc]
    have hn := gb.naturality (ta M)
    have hk := kh.hom.naturality (ar.hom.app M)
    have hd := kd.hom.naturality (ar.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn hk hd
    rw [← Category.assoc (gb.app _), ← hn]
    simp only [Category.assoc]
    rw [hk]
    rw [hd]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ (K.J T.cg.i).map ((K.R T.cf.g).map (ta M)) ≫ k ≫
        (K.R (r.rfh.hom ≫ T.p)).map (ar.hom.app M))
      (hv ((K.J S.cf.i).obj M))
  let l := K.pComp T.p T.cg.g T.cfg.g T.p_g
  let m := K.pComp r.rfh.hom T.cfg.g S.cfg.g r.rfh.hom_g
  let n := K.pComp r.rh.hom T.cg.g S.cg.g r.rh.hom_g
  let o := K.pComp S.p S.cg.g S.cfg.g S.p_g
  let z := K.pComp (r.rfh.hom ≫ T.p) T.cg.g S.cfg.g
    (by rw [Category.assoc, T.p_g, r.rfh.hom_g])
  ext M
  unfold compositionH
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, pastingD_app, pastingC_app, compositionF,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc]
  change
    (K.R T.cg.g).map (gb.app ((K.J T.cf.i).obj M)) ≫
      (K.R T.cg.g).map ((K.R T.p).map (aT.hom.app M)) ≫
      l.hom.app ((K.J T.cfg.i).obj M) ≫
      (K.R T.cfg.g).map ((K.J T.cfg.i).map ((K.rId X).inv.app M)) ≫
      (K.R T.cfg.g).map (ge.app M) ≫
      m.hom.app ((K.J S.cfg.i).obj M) =
    (K.R T.cg.g).map ((K.J T.cg.i).map
      ((K.R T.cf.g).map ((K.J T.cf.i).map ((K.rId X).inv.app M)))) ≫
      (K.R T.cg.g).map ((K.J T.cg.i).map
        ((K.R T.cf.g).map (ga.app M))) ≫
      (K.R T.cg.g).map ((K.J T.cg.i).map
        (pt.hom.app ((K.J S.cf.i).obj M))) ≫
      (K.R T.cg.g).map ((K.J T.cg.i).map
        ((K.rId Y).inv.app ((K.R S.cf.g).obj ((K.J S.cf.i).obj M)))) ≫
      (K.R T.cg.g).map
        (gd.app ((K.R S.cf.g).obj ((K.J S.cf.i).obj M))) ≫
      n.hom.app ((K.J S.cg.i).obj
        ((K.R S.cf.g).obj ((K.J S.cf.i).obj M))) ≫
      (K.R S.cg.g).map (gc.app ((K.J S.cf.i).obj M)) ≫
      (K.R S.cg.g).map ((K.R S.p).map (ar.hom.app M)) ≫
      o.hom.app ((K.J S.cfg.i).obj M)
  have hn₁ := n.hom.naturality (gc.app ((K.J S.cf.i).obj M))
  have hn₂ := n.hom.naturality ((K.R S.p).map (ar.hom.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁ hn₂
  rw [← Category.assoc (n.hom.app _), ← hn₁]
  simp only [Category.assoc]
  rw [← Category.assoc (n.hom.app _), ← hn₂]
  simp only [Category.assoc]
  rw [← K.pAssoc S.p r.rh.hom T.cg.g (r.rfh.hom ≫ T.p) S.cg.g
    S.cfg.g r.p_comm.symm r.rh.hom_g
    (by rw [Category.assoc, T.p_g, r.rfh.hom_g]) S.p_g]
  rw [← Category.assoc ((K.R T.cfg.g).map _), ← Functor.map_comp]
  change
    (K.R T.cg.g).map (gb.app ((K.J T.cf.i).obj M)) ≫
      (K.R T.cg.g).map ((K.R T.p).map (aT.hom.app M)) ≫
      l.hom.app ((K.J T.cfg.i).obj M) ≫
      (K.R T.cfg.g).map (te M) ≫ m.hom.app ((K.J S.cfg.i).obj M) = _
  have hl := l.hom.naturality (te M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hl
  rw [← Category.assoc (l.hom.app _), ← hl]
  simp only [Category.assoc]
  rw [← K.pAssoc r.rfh.hom T.p T.cg.g (r.rfh.hom ≫ T.p) T.cfg.g
    S.cfg.g rfl T.p_g (by rw [Category.assoc, T.p_g, r.rfh.hom_g]) r.rfh.hom_g]
  simp only [← Category.assoc]
  apply (cancel_mono (z.hom.app ((K.J S.cfg.i).obj M))).mpr
  simp only [← Functor.map_comp]
  congr 1
  simpa only [ta, td, Category.assoc, Functor.map_comp] using core M

private theorem baseChange_pasting (K : RawPastingData.{u, v, w})
    {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    Functor.whiskerRight (compositionD K T) (K.G g) ≫ compositionEhf K A =
      compositionHorizontalE K A ≫ Functor.whiskerLeft (K.G x) (compositionD K T') := by
  ext M
  have hA : (K.G A.s).map ((K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom.app M) ≫
      (K.beta x T'.cfg.i T.cfg.i A.s A.cfg_i.w A.cfg_i).hom.app M =
    (K.beta A.d T'.q T.q A.s A.b.w A.b).hom.app ((K.J T.cf.i).obj M) ≫
      (K.J T'.q).map ((K.beta x T'.cf.i T.cf.i A.d A.cf_i.w A.cf_i).hom.app M) ≫
      (K.jCompNamed T'.cf.i T'.q T'.cfg.i T'.i_q).hom.app ((K.G x).obj M) := by
    have transport (i : X ⟶ T.cfg.Z) (i' : X' ⟶ T'.cfg.Z)
        [IsOpenImmersion i] [IsOpenImmersion i']
        (hi : T.cf.i ≫ T.q = i) (hi' : T'.cf.i ≫ T'.q = i')
        (sq : IsPullback x i' i A.s) :
        (K.G A.s).map ((K.jCompNamed T.cf.i T.q i hi).hom.app M) ≫
            (K.beta x i' i A.s sq.w sq).hom.app M =
          (K.beta A.d T'.q T.q A.s A.b.w A.b).hom.app ((K.J T.cf.i).obj M) ≫
            (K.J T'.q).map
              ((K.beta x T'.cf.i T.cf.i A.d A.cf_i.w A.cf_i).hom.app M) ≫
            (K.jCompNamed T'.cf.i T'.q i' hi').hom.app ((K.G x).obj M) := by
      subst i
      subst i'
      have hb := K.beta_open_comp T.cf.i T.q T'.cf.i T'.q A.d x A.s
        A.cf_i.w A.b.w sq.w A.cf_i A.b sq M
      apply (cancel_epi ((K.G A.s).map ((K.jCompNamed T.cf.i T.q (T.cf.i ≫ T.q) rfl).inv.app M))).1
      simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      rw [(K.G A.s).map_id, Category.id_comp]
      simpa only [Category.assoc] using hb.symm
    exact transport T.cfg.i T'.cfg.i T.i_q T'.i_q A.cfg_i
  have hC := K.calculus.2.2
    T.q T.cg.i T.cf.g T.p T'.q T'.cg.i T'.cf.g T'.p
    A.s A.t y A.d T.isPullback.w.symm T'.isPullback.w.symm
    A.b.w A.cg_i.w A.p.w A.cf_g.w A.b A.cg_i A.p A.cf_g ((K.J T.cf.i).obj M)
  have hv := K.proper_pasting A.s A.t g T'.p T.p T'.cg.g T.cg.g T'.cfg.g T.cfg.g
    A.p.w A.cg_g.w T'.p_g T.p_g A.cfg_g.w ((K.J T.cfg.i).obj M)
  unfold compositionHorizontalE compositionEhf compositionEf compositionEh
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    pastingD_app,
    pastingE_app,
    compositionF, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  change
    (K.G g).map ((K.R T.cg.g).map
      ((K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm).app
        ((K.J T.cf.i).obj M))) ≫
      (K.G g).map ((K.R T.cg.g).map ((K.R T.p).map
        ((K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom.app M))) ≫
      (K.G g).map ((K.pComp T.p T.cg.g T.cfg.g T.p_g).hom.app
        ((K.J T.cfg.i).obj M)) ≫
      (K.exchange A.s T'.cfg.g T.cfg.g g A.cfg_g.w).app ((K.J T.cfg.i).obj M) ≫
      (K.R T'.cfg.g).map
        ((K.beta x T'.cfg.i T.cfg.i A.s A.cfg_i.w A.cfg_i).hom.app M) = _
  rw [hv]
  simp only [Category.assoc]
  have hcancel : (K.G g).map ((K.pComp T.p T.cg.g T.cfg.g T.p_g).hom.app
      ((K.J T.cfg.i).obj M)) ≫
      (K.G g).map ((K.pComp T.p T.cg.g T.cfg.g T.p_g).inv.app
        ((K.J T.cfg.i).obj M)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have hn₁ := (K.exchange A.t T'.cg.g T.cg.g g A.cg_g.w).naturality
    ((K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm).app ((K.J T.cf.i).obj M) ≫
      (K.R T.p).map ((K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom.app M))
  have hn₂ := (K.pComp T'.p T'.cg.g T'.cfg.g T'.p_g).hom.naturality
    ((K.beta x T'.cfg.i T.cfg.i A.s A.cfg_i.w A.cfg_i).hom.app M)
  have hn₃ := congrArg (K.R T'.cg.g).map
    ((K.exchange A.s T'.p T.p A.t A.p.w).naturality
      ((K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom.app M))
  have hn₄ := congrArg (K.R T'.cg.g).map
    ((K.gamma T'.q T'.cf.g T'.p T'.cg.i T'.isPullback.w.symm).naturality
      ((K.beta x T'.cf.i T.cf.i A.d A.cf_i.w A.cf_i).hom.app M))
  have hA' := congrArg (fun a ↦ (K.R T'.cg.g).map ((K.R T'.p).map a)) hA
  have hC' := congrArg (K.R T'.cg.g).map hC
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
    at hn₁ hn₂ hn₃ hn₄ hA' hC'
  rw [reassoc_of% hcancel, reassoc_of% hn₁, ← hn₂,
    reassoc_of% hn₃, reassoc_of% hA', reassoc_of% hn₄, reassoc_of% hC']

private theorem refinement_transport (K : RawPastingData.{u, v, w}) {X Y Z : Scheme.{u}} {f : X ⟶
  Y} {h : Y ⟶ Z}
    (T S : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.cfg.i]
    [QuasiCompact T.q]
    [QuasiCompact S.cf.i] [QuasiCompact S.cg.i] [QuasiCompact S.cfg.i]
    [QuasiCompact S.q] (r : CompositionRefinement S T)
    (dT : compositionF K T.cf ⋙ compositionF K T.cg ⟶ compositionF K T.cfg)
    (dS : compositionF K S.cf ⋙ compositionF K S.cg ⟶ compositionF K S.cfg)
    (c : compositionF K T.cfg ⟶ compositionF K S.cfg)
    (hh : compositionF K T.cf ⋙ compositionF K T.cg ⟶
      compositionF K S.cf ⋙ compositionF K S.cg)
    (hdT : compositionD K T = dT) (hdS : compositionD K S = dS)
    (hc : compositionC K r.rfh = c) (hhH : compositionH K r = hh) :
    dT ≫ c = hh ≫ dS := by
  subst dT dS c hh
  exact refinement_pasting K T S r

private theorem baseChange_transport (K : RawPastingData.{u, v, w})
    {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g)
    (dT : compositionF K T.cf ⋙ compositionF K T.cg ⟶ compositionF K T.cfg)
    (dT' : compositionF K T'.cf ⋙ compositionF K T'.cg ⟶ compositionF K T'.cfg)
    (ehf : compositionF K T.cfg ⋙ K.G g ⟶ K.G x ⋙ compositionF K T'.cfg)
    (eh : (compositionF K T.cf ⋙ compositionF K T.cg) ⋙ K.G g ⟶
      K.G x ⋙ (compositionF K T'.cf ⋙ compositionF K T'.cg))
    (hdT : compositionD K T = dT) (hdT' : compositionD K T' = dT')
    (hehf : compositionEhf K A = ehf) (heh : compositionHorizontalE K A = eh) :
    Functor.whiskerRight dT (K.G g) ≫ ehf =
      eh ≫ Functor.whiskerLeft (K.G x) dT' := by
  subst dT dT' ehf eh
  exact baseChange_pasting K T T' A

end RawPastingData
set_option backward.isDefEq.respectTransparency true
private theorem actual_beta_open_comp {V U X V₁ U₁ X₁ : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) (k₁ : V₁ ⟶ U₁) (j₁ : U₁ ⟶ X₁)
    (a : U₁ ⟶ U) (b : V₁ ⟶ V) (g : X₁ ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k₁] [IsOpenImmersion j₁]
    (wk : b ≫ k = k₁ ≫ a) (wj : a ≫ j = j₁ ≫ g)
    (w : b ≫ (k ≫ j) = (k₁ ≫ j₁) ≫ g)
    (sk : IsPullback b k₁ k a) (sj : IsPullback a j₁ j g)
    (s : IsPullback b (k₁ ≫ j₁) (k ≫ j) g) (M : Derived B V) :
    (G B g).map ((jCompNamed B k j (k ≫ j) rfl).inv.app M) ≫
        (beta B a j₁ j g wj sj).hom.app ((J B k).obj M) ≫
        (J B j₁).map ((beta B b k₁ k a wk sk).hom.app M) ≫
        (jCompNamed B k₁ j₁ (k₁ ≫ j₁) rfl).hom.app ((G B b).obj M) =
      (beta B b (k₁ ≫ j₁) (k ≫ j) g w s).hom.app M := by
  simpa only [jCompNamed, jCongr, eqToIso_refl, Iso.trans_refl] using beta_open_comp B k j k₁ j₁ a
    b g wk wj w sk sj s M

private theorem actual_calculus :
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived B A),
      (J B j).map ((pComp B r₁ r₂ (r₁ ≫ r₂) rfl).hom.app M) ≫
          (refinementGamma B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (pComp B p₁ p₂ (p₁ ≫ p₂) rfl).inv.app ((J B k).obj M) =
        (refinementGamma B i r₂ p₂ j h₂).app ((R B r₁).obj M) ≫
          (R B p₂).map ((refinementGamma B k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived B A),
      (jCompNamed B i j (i ≫ j) rfl).hom.app ((R B r).obj M) ≫
          (refinementGamma B (k ≫ l) r q (i ≫ j) h).app M ≫
          (R B q).map ((jCompNamed B k l (k ≫ l) rfl).inv.app M) =
        (J B j).map ((refinementGamma B k r p i h₁).app M) ≫
          (refinementGamma B l p q j h₂).app ((J B k).obj M)) ∧
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (_sp : IsPullback a p₁ p b) (_sr : IsPullback d r₁ r c) (M : Derived B V),
      (G B b).map ((refinementGamma B k r p i h).app M) ≫
          (refinementExchange B a p₁ p b wp).app ((J B k).obj M) ≫
          (R B p₁).map ((beta B d k₁ k a wk sk).hom.app M) =
        (beta B c i₁ i b wi si).hom.app ((R B r).obj M) ≫
          (J B i₁).map ((refinementExchange B d r₁ r c wr).app M) ≫
          (refinementGamma B k₁ r₁ p₁ i₁ h₁).app ((G B d).obj M)) := by
  simpa only [refinementGamma_eq, refinementExchange_app_eq, pComp, rCompEq_eq,
    jCompNamed, jCongr, eqToIso_refl, Iso.trans_refl]
    using normalizedProperOpenCalculus B

private noncomputable def actualPastingData (B : Type (u + 1)) [CommRing B] :
    RawPastingData.{u, u + 2, u + 2} where
  obj := Derived B
  category _ := inferInstance
  R := R B
  G := G B
  J := J B
  rId := rId B
  pComp := pComp B
  jCompNamed := jCompNamed B
  gamma := refinementGamma B
  beta := beta B
  exchange := refinementExchange B
  pAssoc := pAssoc B
  pRight := pRight B
  beta_open_comp := actual_beta_open_comp B
  calculus := actual_calculus B
  proper_pasting := proper_pasting B

private theorem refinement_pasting {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T S : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.cfg.i]
    [QuasiCompact T.q]
    [QuasiCompact S.cf.i] [QuasiCompact S.cg.i] [QuasiCompact S.cfg.i]
    [QuasiCompact S.q] (r : CompositionRefinement S T) :
    compositionD B T ≫ compositionC B r.rfh =
      compositionH B r ≫ compositionD B S := by
  exact RawPastingData.refinement_transport (actualPastingData B) T S r
    (compositionD B T) (compositionD B S) (compositionC B r.rfh) (compositionH B r)
    (by
      dsimp only [RawPastingData.compositionD, actualPastingData, compositionD, pComp, jCompNamed]
      simp only [refinementGamma_eq, rCompEq_eq, Iso.trans_hom]
      rfl)
    (by
      dsimp only [RawPastingData.compositionD, actualPastingData, compositionD, pComp, jCompNamed]
      simp only [refinementGamma_eq, rCompEq_eq, Iso.trans_hom]
      rfl)
    (by
      dsimp only [RawPastingData.compositionC, actualPastingData, compositionC, pComp]
      simp only [refinementGamma_eq, rCompEq_eq, Iso.trans_hom]
      rfl)
    (by
      dsimp only [RawPastingData.compositionH, compositionH, RawPastingData.compositionC,
        RawPastingData.compositionF, compositionC, compositionF, actualPastingData, pComp]
      simp only [refinementGamma_eq, rCompEq_eq, Iso.trans_hom])

private theorem baseChange_pasting
    {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} {f' : X' ⟶ Y'} {h' : Y' ⟶ Z'}
    (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
    {x : X' ⟶ X} {y : Y' ⟶ Y} {g : Z' ⟶ Z}
    (A : CompositionBaseChange T T' x y g) :
    Functor.whiskerRight (compositionD B T) (G B g) ≫ compositionEhf B A =
      compositionHorizontalE B A ≫ Functor.whiskerLeft (G B x) (compositionD B T') := by
  exact RawPastingData.baseChange_transport (actualPastingData B) T T' A
    (compositionD B T) (compositionD B T') (compositionEhf B A) (compositionHorizontalE B A)
    (by
      dsimp only [RawPastingData.compositionD, actualPastingData, compositionD, pComp, jCompNamed]
      simp only [refinementGamma_eq, rCompEq_eq, Iso.trans_hom]
      rfl)
    (by
      dsimp only [RawPastingData.compositionD, actualPastingData, compositionD, pComp, jCompNamed]
      simp only [refinementGamma_eq, rCompEq_eq, Iso.trans_hom]
      rfl)
    (by
      dsimp only [RawPastingData.compositionEhf, RawPastingData.compositionE, actualPastingData,
        compositionEhf, compositionE]
      simp only [refinementExchange_app_eq]
      rfl)
    (by
      dsimp only [RawPastingData.compositionHorizontalE, RawPastingData.compositionEf,
        RawPastingData.compositionEh, RawPastingData.compositionE, RawPastingData.compositionF,
        actualPastingData, compositionHorizontalE, compositionEf, compositionEh, compositionE,
        compositionF]
      simp only [refinementExchange_app_eq])
end PastingCalculation

private theorem finiteOrigin_open {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : Derived B U)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B U ((ev B U n).obj M))) :
    ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj ((J B j).obj M))) := by
  intro n
  classical
  let w := Classical.choice (hM n)
  let L := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} w.Λ) j).mapDerivedCategoryPlus.obj
    w.origin.L
  let F := (finiteCoefficientComparison X w.Λ).mapDerivedCategoryPlus.obj L
  let w' : ScalarEtaleOrigin B X
      ((finiteRestriction B X w.Λ w.φ).mapDerivedCategory.obj F.obj) :=
    { Λ := w.Λ
      φ := w.φ
      F := F
      origin := ⟨L, Iso.refl _⟩
      iso := Iso.refl _ }
  exact ⟨{ w' with iso := (originIso B w').symm ≪≫
    (hJ B j w.Λ w.φ).app w.origin.L ≪≫
    (moduleJ B j).mapDerivedCategory.mapIso (originIso B w) ≪≫
    ((evalJ B j n).app M).symm }⟩

private theorem compositionFactor_isIso {A C D E F H : Type*}
    [Category A] [Category C] [Category D] [Category E] [Category F] [Category H]
    (J₀ : A ⥤ C) (J₁ : C ⥤ D) (J₂ : A ⥤ D)
    (P : C ⥤ E) (K : E ⥤ F) (L : D ⥤ F) (Q : F ⥤ H) (S : D ⥤ H)
    (g : P ⋙ K ⟶ J₁ ⋙ L) (e : J₀ ⋙ J₁ ≅ J₂) (v : L ⋙ Q ≅ S)
    (a : J₀ ⋙ P ⋙ K ⋙ Q ⟶ J₂ ⋙ S)
    (ha : a = Functor.whiskerLeft J₀ (Functor.whiskerRight g Q) ≫
      Functor.whiskerRight e.hom (L ⋙ Q) ≫ Functor.whiskerLeft J₂ v.hom)
    (M : A) (hg : IsIso (g.app (J₀.obj M))) : IsIso (a.app M) := by
  subst a
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- Composition pasting is invertible on the stated finite-origin inputs, commutes with
all compatible proper refinements, and satisfies vertical interchange under arbitrary
base change. The latter two clauses are equalities of natural transformations on the
whole derived strict-tower categories; no evaluation-faithfulness premise is made.

Source: Stacks, Tags 0F7J, 0F7C, 0F7D and 0F7F, adapted to strict towers
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence).

Proof plan, following the node's ten steps:
1. Evaluation commutes with J_c. A scalar etale origin L_n evaluates J_c M as the
   scalar realization of c_! L_n, by finite constant coefficient transport and
   proposition-comparison-immersions--1. Exactness of etale c_!
   (lem-weil-pbc-extension-by-zero-exact) retains its individual lower bound.
2. Apply gamma_isIso to Q at J_c M, and whisker with R_q. The jComp and rComp
   identifications give exactly compositionD, naturally in M.
3. For a refinement let A be its c-square, H its i-square, and T its b-square.
   Horizontal pasting in normalizedProperOpenCalculus gives
   gamma_a = (gamma_T J_c1)(J_b2 gamma_A). T need not be cartesian.
4. Apply vertical pasting to T above Q2 and Q1 above H; their outer squares agree.
   Thus (R_p2 gamma_T)(gamma_Q2 R_w) = (R_u gamma_Q1)(gamma_H R_r1).
5. Naturality of gamma_Q2 at gamma_A moves gamma_A past gamma_Q2.
6. Expand C_hf D2 using step 3, then steps 5 and 4. Normalize R_q2 R_u to R_q1.
   The result is D1 (C_h F_f1)(F_h2 C_f), with the displayed associators.
7. For base change, mate-pasting identifies E_qp with (R_q' E_p)(E_q R_p).
   Open composition identifies beta_a with (J_b' beta_c)(beta_b J_c).
8. The base-change clause of normalizedProperOpenCalculus gives
   (R_p' beta_b)(E_p J_b)(G_t gamma_Q)
     = (gamma_Q' G_d)(J_i' E_r)(beta_i R_r).
9. In e_hf(G_g D), naturality of E_q moves gamma_Q inside R_q'. Apply step 8.
   Naturality of gamma_Q' at beta_c leaves precisely
   (D' G_x)(F_h' e_f)(e_h F_f), proving vertical interchange before evaluation.
10. The same calculus cube on refinement squares transports both boundaries;
    common-refinement and independence are recorded below. No common bound or
    finite coefficient ring for all levels, and no properness of the base change,
    is used anywhere.
-/
theorem compositionPastingCoherence :
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Triangle f h)
      [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
      (M : Derived B X),
      (∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) →
      IsIso ((compositionD B T).app M)) ∧
    (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T₁ T₂ : Compactification.Triangle f h)
      [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
      [QuasiCompact T₁.q]
      [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
      [QuasiCompact T₂.q] (r : CompositionRefinement T₁ T₂),
      compositionD B T₂ ≫ compositionC B r.rfh =
        compositionH B r ≫ compositionD B T₁) ∧
    (∀ {X Y Z X' Y' Z' : Scheme.{u}}
      (f : X ⟶ Y) (h : Y ⟶ Z) (f' : X' ⟶ Y') (h' : Y' ⟶ Z')
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
      [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
      [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
      (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z)
      (A : CompositionBaseChange T T' x y g),
      Functor.whiskerRight (compositionD B T) (G B g) ≫ compositionEhf B A =
        compositionHorizontalE B A ≫ Functor.whiskerLeft (G B x) (compositionD B T')) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z f h _ _ _ _ _ _ T _ _ _ M hM
    exact compositionFactor_isIso (J B T.cf.i) (J B T.q) (J B T.cfg.i)
      (R B T.cf.g) (J B T.cg.i) (R B T.p) (R B T.cg.g) (R B T.cfg.g)
      (gamma B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (jComp B T.cf.i T.q ≪≫ jCongr B T.i_q)
      (rComp B T.p T.cg.g ≪≫ eqToIso (congrArg (R B) T.p_g))
      (compositionD B T) rfl M
      (gamma_isIso B T.q T.cf.g T.p T.cg.i T.isPullback.w.symm
        ((J B T.cf.i).obj M) (finiteOrigin_open B T.cf.i M hM))
  · intro X Y Z f h _ _ _ _ _ _ T₁ T₂ _ _ _ _ _ _ _ _ r
    exact refinement_pasting B T₂ T₁ r
  · intro X Y Z X' Y' Z' f h f' h' _ _ _ _ _ _ T T' _ _ _ _ _ _ x y g A
    exact baseChange_pasting B T T' A

attribute [local irreducible] G R J adj jAdj rComp jComp rId gamma beta exchange
set_option backward.isDefEq.respectTransparency true

private theorem refinementFactor_isIso {A C D E : Type*}
    [Category A] [Category C] [Category D] [Category E]
    (J₁ : A ⥤ C) (J₂ : A ⥤ D) (R₀ : A ⥤ A) (R₁ : C ⥤ D) (R₂ : D ⥤ E)
    (H : C ⥤ E) (e₀ : R₀ ≅ 𝟭 A) (e₁ : R₁ ⋙ R₂ ≅ H)
    (g : R₀ ⋙ J₂ ⟶ J₁ ⋙ R₁) (a : J₂ ⋙ R₂ ⟶ J₁ ⋙ H)
    (ha : a = Functor.whiskerRight
        (Functor.whiskerRight e₀.inv J₂ ≫ g) R₂ ≫
      Functor.whiskerLeft J₁ e₁.hom)
    (M : A) (hg : IsIso (g.app M)) : IsIso (a.app M) := by
  subst a
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- Both boundaries of the refinement square are invertible on finite-origin objects.
Source: Stacks, Tag 0F7J, choice independence
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence).
Proof: apply gamma_isIso to the refinement square for the compactifications of hf;
its left proper map is identity. Whisker by the outer proper direct image to obtain
invertibility of C_hf. By compositionPastingCoherence both D's are invertible and
C_hf D2 = D1 H, so H = D1⁻¹ C_hf D2 is invertible. This avoids any finite-origin
assumption on F_f M, as in step 10 of the node. -/
theorem compositionRefinement_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T₁ T₂ : Compactification.Triangle f h)
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
    [QuasiCompact T₁.q]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
    [QuasiCompact T₂.q] (r : CompositionRefinement T₁ T₂) (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    IsIso ((compositionC B r.rfh).app M) ∧ IsIso ((compositionH B r).app M) := by
  have hc : IsIso ((compositionC B r.rfh).app M) :=
    refinementFactor_isIso (J B T₁.cfg.i) (J B T₂.cfg.i) (R B (𝟙 X))
      (R B r.rfh.hom) (R B T₂.cfg.g) (R B T₁.cfg.g) (rId B X)
      (rComp B r.rfh.hom T₂.cfg.g ≪≫ eqToIso (congrArg (R B) r.rfh.hom_g))
      (gamma B T₁.cfg.i (𝟙 X) r.rfh.hom T₂.cfg.i
        (r.rfh.i_hom.trans (Category.id_comp T₂.cfg.i).symm))
      (compositionC B r.rfh) rfl M
      (gamma_isIso B T₁.cfg.i (𝟙 X) r.rfh.hom T₂.cfg.i
        (r.rfh.i_hom.trans (Category.id_comp T₂.cfg.i).symm) M hM)
  have hd₁ := (compositionPastingCoherence B).1 f h T₁ M hM
  have hd₂ := (compositionPastingCoherence B).1 f h T₂ M hM
  have heq := congrArg (fun η => η.app M)
    ((compositionPastingCoherence B).2.1 f h T₁ T₂ r)
  simp only [NatTrans.comp_app] at heq
  have hh : IsIso ((compositionH B r).app M ≫ (compositionD B T₁).app M) := by
    rw [← heq]
    infer_instance
  exact ⟨hc, IsIso.of_isIso_comp_right _ ((compositionD B T₁).app M)⟩

/-- The horizontal and hf comparisons from a common refining compatible tower, on a
finite-origin input. In the node's right-to-left convention they are H₂⁻¹H₁ and C₂⁻¹C₁.
Source: Stacks, Tag 0F7J, common refinements
(blueprint: lem-cbc-complete-proetale-composition-pasting-coherence). -/
noncomputable def compositionCommonComparison
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (T₁ T₂ S : Compactification.Triangle f h)
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i] [QuasiCompact T₁.cfg.i]
    [QuasiCompact T₁.q]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i] [QuasiCompact T₂.cfg.i]
    [QuasiCompact T₂.q]
    [QuasiCompact S.cf.i] [QuasiCompact S.cg.i] [QuasiCompact S.cfg.i]
    [QuasiCompact S.q]
    (r₁ : CompositionRefinement S T₁) (r₂ : CompositionRefinement S T₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    (((compositionF B T₁.cf ⋙ compositionF B T₁.cg).obj M ⟶
      (compositionF B T₂.cf ⋙ compositionF B T₂.cg).obj M) ×
      ((compositionF B T₁.cfg).obj M ⟶ (compositionF B T₂.cfg).obj M)) :=
  ⟨(compositionH B r₁).app M ≫
      @inv _ _ _ _ ((compositionH B r₂).app M)
        (compositionRefinement_isIso B f h S T₂ r₂ M hM).2,
    (compositionC B r₁.rfh).app M ≫
      @inv _ _ _ _ ((compositionC B r₂.rfh).app M)
        (compositionRefinement_isIso B f h S T₂ r₂ M hM).1⟩

section CommonComparisonProof

set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible]
  compositionD compositionC compositionH compositionCommonComparison

end CommonComparisonProof

end AlgebraicGeometry.ProEtale.StrictTower
