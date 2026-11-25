/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Global inverse-image section restriction through a square

Source: Stacks Project, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-global-section-square).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

local notation "L" => Scheme.etaleSetPullback
local notation "I[" X "]" => Scheme.Etale.mk (𝟙 X)
set_option quotPrecheck false in
local notation "η[" X "," Y "]" e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ e) _
      (Scheme.smallGrothendieckTopology @Etale X)
      (Scheme.smallGrothendieckTopology @Etale Y))
set_option quotPrecheck false in
local notation "R[" X "," Y "," e "," G "]" =>
  (((η[X,Y] e).app G).hom.app (op I[X]) ≫
    ((L e).obj G).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift e (𝟙 Y)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp <;> rfl) :
        I[Y] ⟶ (MorphismProperty.Over.pullback @Etale ⊤ e).obj I[X]).op)

set_option quotPrecheck false in
local notation "P[" f "," k "," r "," hk "," F "]" =>
  (fun a => Eq.mp
    (congrArg (fun e => ((L e).obj F).obj.obj (op I[_])) (show k ≫ f = r from hk))
    ((((Classical.choose etaleSetInverseImageCompositionUnits.2.2
      _ _ _ f k).hom.app F).hom.app (op I[_]))
      (R[_,_,k,(L f).obj F] a)))

private noncomputable def terminalLift {X Y : Scheme.{u}} (e : Y ⟶ X) :
    I[Y] ⟶ (MorphismProperty.Over.pullback @Etale ⊤ e).obj I[X] :=
  MorphismProperty.Over.homMk
    (pullback.lift e (𝟙 Y)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp)

private noncomputable def restrict {X Y : Scheme.{u}} (e : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (a : G.obj.obj (op I[X])) : ((L e).obj G).obj.obj (op I[Y]) :=
  ((L e).obj G).obj.map (terminalLift e).op
    (((η[X,Y] e).app G).hom.app (op I[X]) a)

private noncomputable def comparison {X Y W : Scheme.{u}} (f : Y ⟶ X) (k : W ⟶ Y) :=
  Classical.choose etaleSetInverseImageCompositionUnits.2.2 X Y W f k

set_option backward.isDefEq.respectTransparency false in
private lemma restrict_natural {X Y : Scheme.{u}} (e : Y ⟶ X)
    (G G' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : G ⟶ G')
    (a : G.obj.obj (op I[X])) :
    restrict e G' (ψ.hom.app (op I[X]) a) =
      ((L e).map ψ).hom.app (op I[Y]) (restrict e G a) := by
  unfold restrict
  rw [etaleSetInverseImageCompositionUnits.2.1 X Y e G G' ψ I[X] a]
  exact ConcreteCategory.congr_hom
    (((L e).map ψ).hom.naturality (terminalLift e).op).symm _

set_option backward.isDefEq.respectTransparency false in
private lemma restrict_comp {X Y W : Scheme.{u}} (f : Y ⟶ X) (k : W ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (a : G.obj.obj (op I[X])) :
    ((comparison f k).hom.app G).hom.app (op I[W])
      (restrict k ((L f).obj G) (restrict f G a)) = restrict (k ≫ f) G a := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ k
  let m := terminalLift k ≫ b.map (terminalLift f)
  have hm : m ≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) k f).inv.app I[X] =
      terminalLift (k ≫ f) := by
    exact (IsTerminal.isTerminalObj
      (MorphismProperty.Over.pullback @Etale ⊤ (k ≫ f)) I[X]
      (MorphismProperty.Over.mkIdTerminal (P := @Etale) X)).hom_ext _ _
  have hu := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
    X Y W f k G I[X] a
  have hu' := congrArg (((L (k ≫ f)).obj G).obj.map m.op) hu
  have hc := ((comparison f k).hom.app G).hom.naturality m.op
  have hn := etaleSetInverseImageCompositionUnits.1 Y W k ((L f).obj G)
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj I[X]) I[Y]
    (terminalLift f) (((η[X,Y] f).app G).hom.app (op I[X]) a)
  have hce := ConcreteCategory.congr_hom hc
    (((η[Y,W] k).app ((L f).obj G)).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj I[X]))
      (((η[X,Y] f).app G).hom.app (op I[X]) a))
  have H := hce.trans hu'
  unfold restrict
  rw [hn]
  simp only [CategoryTheory.types_comp_apply] at H
  have hmap := ((L (k ≫ f)).obj G).obj.map_comp
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) k f).inv.app I[X]).op
    m.op
  have Hmap := ConcreteCategory.congr_hom hmap
    (((η[X,W] (k ≫ f)).app G).hom.app (op I[X]) a)
  simp only [CategoryTheory.types_comp_apply] at Hmap
  erw [← Hmap] at H
  simp only [← op_comp] at H
  erw [hm] at H
  simpa only [m, b, op_comp, Functor.comp_obj, Functor.map_comp,
    CategoryTheory.types_comp_apply] using H

private lemma section_eqToHom {S E : Scheme.{u}} (f g : E ⟶ S) (he : f = g)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (X : E.Etale)
    (a : ((L f).obj F).obj.obj (op X)) :
    ((eqToHom (congrArg (fun k => (L k).obj F) he)).hom.app (op X)) a =
      Eq.mp (congrArg (fun k => ((L k).obj F).obj.obj (op X)) he) a := by
  cases he
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma section_comp {S T D E : Scheme.{u}} (f : T ⟶ S) (k : D ⟶ T)
    (d : E ⟶ D) (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (a : ((L f).obj F).obj.obj (op I[T])) :
    P[k ≫ f,d,d ≫ k ≫ f,rfl,F] (P[f,k,k ≫ f,rfl,F] a) =
      P[f,d ≫ k,d ≫ k ≫ f,(Category.assoc d k f),F] a := by
  have hassoc := (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
    S T D E f k d F
  have H := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun ψ => ψ.hom) hassoc) (op I[E]))
      (restrict d ((L k).obj ((L f).obj F)) (restrict k ((L f).obj F) a))
  change
    ((comparison (k ≫ f) d).hom.app F).hom.app (op I[E])
      (((L d).map ((comparison f k).hom.app F)).hom.app (op I[E])
        (restrict d ((L k).obj ((L f).obj F)) (restrict k ((L f).obj F) a))) =
    ((eqToHom (congrArg (fun j => (L j).obj F) (Category.assoc d k f))).hom.app
      (op I[E]))
      (((comparison f (d ≫ k)).hom.app F).hom.app (op I[E])
        (((comparison k d).hom.app ((L f).obj F)).hom.app (op I[E])
          (restrict d ((L k).obj ((L f).obj F)) (restrict k ((L f).obj F) a)))) at H
  rw [restrict_comp] at H
  rw [section_eqToHom ((d ≫ k) ≫ f) (d ≫ k ≫ f) (Category.assoc d k f)] at H
  have hn := restrict_natural d ((L k).obj ((L f).obj F)) ((L (k ≫ f)).obj F)
    ((comparison f k).hom.app F) (restrict k ((L f).obj F) a)
  change
    ((comparison (k ≫ f) d).hom.app F).hom.app (op I[E])
      (restrict d ((L (k ≫ f)).obj F)
        (((comparison f k).hom.app F).hom.app (op I[D])
          (restrict k ((L f).obj F) a))) = _
  erw [hn]
  exact H

set_option backward.isDefEq.respectTransparency false in
/-- Global inverse-image section restriction is independent of a factorization through
an arbitrary commutative square. No fibre, field, or connectedness hypothesis is used.

Source: Stacks Project, Sites, Tags 03CB and 03CC; Tag 0A3H, the identification of
restrictions along the two factorizations through a geometric fibre.
(blueprint: lem-weil-pbc-etale-global-section-square).

Proof:
Use unit naturality to move the terminal-object restriction through the component of
the first composition comparison. Apply associativity of the unit-compatible
composition comparisons to rewrite each side as the comparison along the composite
map applied to its direct unit-restriction of a. The unit equation identifies iterated
units with that direct unit. The terminal lifts in the iterated and direct pullbacks
agree because their common target is the pullback of the terminal etale object,
which is terminal since the base-change functor preserves finite limits. The equality of
composite maps supplied by the square then identifies the two expressions. All
Eq.mp transports are along the stated equalities, so proof irrelevance makes their
choices immaterial. This argument applies also to empty schemes. -/
theorem etaleSet_globalSection_square
    {S T D U E : Scheme.{u}} (f : T ⟶ S) (k : D ⟶ T) (d : E ⟶ D)
    (p : U ⟶ T) (v : E ⟶ U) (g : D ⟶ S) (r : U ⟶ S) (t : E ⟶ S)
    (hk : k ≫ f = g) (hp : p ≫ f = r)
    (hd : d ≫ g = t) (hv : v ≫ r = t) (hsq : d ≫ k = v ≫ p)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (a : ((L f).obj F).obj.obj (op I[T])) :
    P[g,d,t,hd,F] (P[f,k,g,hk,F] a) =
      P[r,v,t,hv,F] (P[f,p,r,hp,F] a) := by
  classical
  rcases hk with rfl
  rcases hp with rfl
  rcases hd with rfl
  have H₁ := section_comp f k d F a
  have H₂ := section_comp f p v F a
  change P[k ≫ f,d,d ≫ k ≫ f,rfl,F] (P[f,k,k ≫ f,rfl,F] a) =
    Eq.mp (congrArg (fun j => ((L j).obj F).obj.obj (op I[E])) hv)
      (P[p ≫ f,v,v ≫ p ≫ f,rfl,F] (P[f,p,p ≫ f,rfl,F] a))
  rw [H₁, H₂]
  have hm {A B C : Type (u + 1)} (hab : A = B) (hbc : B = C) (x : A) :
      Eq.mp hbc (Eq.mp hab x) = Eq.mp (hab.trans hbc) x := by
    cases hab
    cases hbc
    rfl
  dsimp only
  rw [hm]
  have hj (j j' : E ⟶ T) (hjj : j = j') :
      Eq.mp (congrArg (fun z => ((L (z ≫ f)).obj F).obj.obj (op I[E])) hjj)
        (((comparison f j).hom.app F).hom.app (op I[E])
          (restrict j ((L f).obj F) a)) =
      ((comparison f j').hom.app F).hom.app (op I[E])
        (restrict j' ((L f).obj F) a) := by
    cases hjj
    rfl
  have H := hj (v ≫ p) (d ≫ k) hsq.symm
  have hh := congrArg
    (Eq.mp (congrArg (fun j => ((L j).obj F).obj.obj (op I[E]))
      (Category.assoc d k f))) H
  simp only [hm] at hh
  exact hh.symm

end AlgebraicGeometry
