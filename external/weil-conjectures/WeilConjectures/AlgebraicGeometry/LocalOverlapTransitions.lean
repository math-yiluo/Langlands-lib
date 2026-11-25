/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # Natural overlap maps before imposing the cocycle

Source: Stacks Project, Tag 01ZR, first proof, Zariski gluing.
(blueprint: def-pc-local-overlap-transitions). -/

@[expose] public section

universe u v t u' v'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Natural overlap maps, with neither identity nor cocycle equations imposed.
These are the maps obtained by gluing lifts on affine overlap charts.
(blueprint: def-pc-local-overlap-transitions). -/
structure OverlapTransitions where
  obj (i : ι) : F.obj (.mk (op (X i)))
  hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
      (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶
        (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)
  pullHom_hom ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    (hq : g ≫ q = q') ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
      pullHom (hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂ =
        hom q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
          (by rw [← hgf₂, Category.assoc, hf₂, hq])

namespace OverlapTransitions

variable {F f}

/-- The two remaining equations for natural overlap maps.
(blueprint: def-pc-local-overlap-transitions)
-/
structure Coherent (T : F.OverlapTransitions f) : Prop where
  hom_self ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    T.hom q g g hg hg = 𝟙 _
  hom_comp ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    T.hom q f₁ f₂ hf₁ hf₂ ≫ T.hom q f₂ f₃ hf₂ hf₃ = T.hom q f₁ f₃ hf₁ hf₃

/-- Assemble the descent datum from the natural maps and their two equations.
(blueprint: def-pc-local-overlap-transitions)
-/
def toDescentData (T : F.OverlapTransitions f) (h : T.Coherent) : F.DescentData f where
  obj := T.obj
  hom := T.hom
  pullHom_hom := T.pullHom_hom
  hom_self := h.hom_self
  hom_comp := h.hom_comp

/-- A component comparison commuting with natural overlap maps.
(blueprint: def-pc-local-overlap-transitions)
-/
structure Comparison (T : F.OverlapTransitions f) (D : F.DescentData f) where
  e (i : ι) : T.obj i ≅ D.obj i
  comm ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D.hom q f₁ f₂ hf₁ hf₂ =
      T.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom

/-- An invertible component comparison with genuine descent data implies coherence.
This supplies the limit equations used by eventual equality.
(blueprint: def-pc-local-overlap-transitions)
-/
lemma Comparison.coherent {T : F.OverlapTransitions f} {D : F.DescentData f}
    (ε : T.Comparison D) : T.Coherent where
  hom_self Y q i g hg := by
    apply (cancel_mono ((F.map g.op.toLoc).toFunctor.map (ε.e _).hom)).mp
    simpa only [D.hom_self q g hg, Category.comp_id, Category.id_comp] using
      (ε.comm q g g hg hg).symm
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    apply (cancel_mono ((F.map f₃.op.toLoc).toFunctor.map (ε.e _).hom)).mp
    rw [Category.assoc, ← ε.comm q f₂ f₃ hf₂ hf₃, ← Category.assoc,
      ← ε.comm q f₁ f₂ hf₁ hf₂, Category.assoc, D.hom_comp, ε.comm q f₁ f₃ hf₁ hf₃]

variable {S' : C} {p : S' ⟶ S} {ι' : Type t} {X' : ι' → C}
  {f' : ∀ j, X' j ⟶ S'} {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
  (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

/-- Pullback of the overlap maps using the pseudofunctor composition comparison.
(blueprint: def-pc-local-overlap-transitions)
-/
def pulledHom (T : F.OverlapTransitions f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (hf₁ : f₁ ≫ f' j₁ = q) (hf₂ : f₂ ≫ f' j₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.obj ((F.map (p' j₁).op.toLoc).toFunctor.obj
      (T.obj (α j₁))) ⟶
    (F.map f₂.op.toLoc).toFunctor.obj ((F.map (p' j₂).op.toLoc).toFunctor.obj
      (T.obj (α j₂))) :=
  (F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).inv.toNatTrans.app _ ≫
    T.hom (q ≫ p) (f₁ ≫ p' _) (f₂ ≫ p' _) (by simp [w, reassoc_of% hf₁])
      (by simp [w, reassoc_of% hf₂]) ≫
    (F.mapComp (p' j₂).op.toLoc f₂.op.toLoc).hom.toNatTrans.app _

set_option backward.isDefEq.respectTransparency false in
/-- Express the pulled overlap map using specified composite arrows.
(blueprint: def-pc-local-overlap-transitions)
-/
lemma pulledHom_eq (T : F.OverlapTransitions f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (q' : Y ⟶ S) (f₁' : Y ⟶ X (α j₁)) (f₂' : Y ⟶ X (α j₂))
    (hf₁ : f₁ ≫ f' j₁ = q) (hf₂ : f₂ ≫ f' j₂ = q)
    (hq' : q ≫ p = q') (hf₁' : f₁ ≫ p' j₁ = f₁') (hf₂' : f₂ ≫ p' j₂ = f₂') :
    pulledHom w T q f₁ f₂ hf₁ hf₂ =
    (F.mapComp' _ _ _).inv.toNatTrans.app _ ≫
      T.hom q' f₁' f₂' (by rw [← hq', ← hf₁', Category.assoc, w, reassoc_of% hf₁])
        (by rw [← hq', ← hf₂', Category.assoc, w, reassoc_of% hf₂]) ≫
      (F.mapComp' _ _ _).hom.toNatTrans.app _ := by
  subst hq' hf₁' hf₂'
  simp [mapComp'_eq_mapComp, pulledHom]

set_option backward.isDefEq.respectTransparency false in
/-- Base change of natural overlap maps. No coherence assumption is required.
(blueprint: def-pc-local-overlap-transitions)
-/
def pull (T : F.OverlapTransitions f) : F.OverlapTransitions f' where
  obj j := (F.map (p' j).op.toLoc).toFunctor.obj (T.obj (α j))
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := pulledHom w T q f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pulledHom_eq _ _ _ _ _ (q' ≫ p) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
        (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) rfl rfl rfl,
      pulledHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
        hf₁ hf₂ rfl rfl rfl]
    rw [← T.pullHom_hom g (q ≫ p) (q' ≫ p) (by rw [reassoc_of% hq])
      (f₁ ≫ p' j₁) (f₂ ≫ p' j₂) (by rw [Category.assoc, w, reassoc_of% hf₁])
      (by rw [Category.assoc, w, reassoc_of% hf₂]) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
      (by cat_disch) (by cat_disch)]
    dsimp [pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _ (by cat_disch),
      mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ _ (by cat_disch)]

/-- Assemble a morphism from a pulled coherent datum using a raw component comparison.
Keeping this construction generic avoids unfolding the concrete cover maps.
(blueprint: def-pc-local-overlap-transitions)
-/
def pullComparisonHom (T : F.OverlapTransitions f) (h : T.Coherent)
    {D : F.DescentData f'} (ε : (T.pull w).Comparison D) :
    (DescentData.pullFunctor F w).obj (T.toDescentData h) ⟶ D where
  hom a := (ε.e a).hom
  comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
    simpa only [pull, pulledHom, DescentData.pullFunctor, DescentData.pullFunctorObj,
      DescentData.pullFunctorObjHom, toDescentData, hf₁] using ε.comm q f₁ f₂ hf₁ hf₂

/-- Every component of the assembled morphism is the hom of a component iso.
(blueprint: def-pc-local-overlap-transitions)
-/
lemma pullComparisonHom_isIso_hom (T : F.OverlapTransitions f) (h : T.Coherent)
    {D : F.DescentData f'} (ε : (T.pull w).Comparison D) (a : ι') :
    IsIso ((T.pullComparisonHom w h ε).hom a) := (ε.e a).isIso_hom

end OverlapTransitions
end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry

/-- The canonical map between two base changes of a cover chart.
(blueprint: def-pc-local-overlap-transitions)
-/
noncomputable def overlapRefinementHom {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (q' : Z ⟶ X) (r : Z ⟶ Y) (h : r ≫ q = q') (a : U.I₀) :
    (U.pullback₁ q').X a ⟶ (U.pullback₁ q).X a :=
  pullback.lift ((U.pullback₁ q').f a ≫ r) (U.pullbackHom q' a) (by
    rw [Category.assoc, h, U.pullbackHom_map])

/-- The canonical chart map lies over the later base-change map.
(blueprint: def-pc-local-overlap-transitions)
-/
lemma overlapRefinementHom_map {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (q' : Z ⟶ X) (r : Z ⟶ Y) (h : r ≫ q = q') (a : U.I₀) :
    overlapRefinementHom U q q' r h a ≫ (U.pullback₁ q).f a =
      (U.pullback₁ q').f a ≫ r := by
  apply pullback.lift_fst

/-- Composition of the refinement chart map with the original chart projection.
(blueprint: def-pc-local-overlap-transitions)
-/
lemma overlapRefinementHom_comp {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (q' : Z ⟶ X) (r : Z ⟶ Y) (h : r ≫ q = q') (a : U.I₀) :
    overlapRefinementHom U q q' r h a ≫ U.pullbackHom q a = U.pullbackHom q' a := by
  apply pullback.lift_snd

/-- A stage transition for the fixed base-changed scheme.
(blueprint: def-pc-local-overlap-transitions)
-/
noncomputable def overlapStageMap {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) {i j k : I} {Xi : Scheme.{u}}
    (f : Xi ⟶ Spec (R.obj i)) (hij : i ≤ j) (hjk : j ≤ k) :=
  baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))

/-- The limit projection for the fixed base-changed scheme.
(blueprint: def-pc-local-overlap-transitions)
-/
noncomputable def overlapLimitMap {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cone (R.op ⋙ Scheme.Spec))
    {i j : I} {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i)) (hij : i ≤ j) :=
  baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))

/-- Stage transitions compose.
(blueprint: def-pc-local-overlap-transitions)
-/
lemma overlapStageMap_comp {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) {i j k l : I} {Xi : Scheme.{u}}
    (f : Xi ⟶ Spec (R.obj i)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    overlapStageMap R f (hij.trans hjk) hkl ≫ overlapStageMap R f hij hjk =
      overlapStageMap R f hij (hjk.trans hkl) := by
  dsimp only [overlapStageMap]
  rw [← baseChangeMap_comp]
  congr 1
  ext
  change Spec.map (R.map (homOfLE hkl)) ≫ Spec.map (R.map (homOfLE hjk)) =
    Spec.map (R.map (homOfLE (hjk.trans hkl)))
  rw [← Spec.map_comp, ← R.map_comp]
  rfl

end AlgebraicGeometry
