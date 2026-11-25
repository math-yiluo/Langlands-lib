/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapConjugateRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import WeilConjectures.AlgebraicGeometry.OverlapStageModelRestriction

/-! # The fixed overlap model and its canonical comparison

Source: Stacks Project, Tag 01ZR (2), first proof, restriction to an overlap.
(blueprint: lem-pc-overlap-pair-model-transport). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

noncomputable section

set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The tensor and abstract pullbacks are canonically identified by their adjunctions.
Source: Stacks Project, Tag 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapTensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
  overlapAdjunctionComparison p

variable {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
  (c : Cone (R.op ⋙ Scheme.Spec)) {i : I} {Xi : Scheme.{u}}
  (f : Xi ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j)
  (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
  (a b : U.I₀)

/-- The structure map of the fixed universal overlap to its stage base.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelHom : pullback (U.f a) (U.f b) ⟶ Spec (R.obj j) :=
  pullback.fst (U.f a) (U.f b) ≫ U.f a ≫
    pullback.snd f (Spec.map (R.map (homOfLE hij)))

/-- A chart projection from the identity base change of the overlap.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelChart (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d) :
    pullback (overlapModelHom R f hij U a b)
      (Spec.map (R.map (homOfLE (le_refl j)))) ⟶ U.X d :=
  pullback.fst _ _ ≫ r

/-- The map from the limit overlap model to the original limit scheme.
It is the universal lift with the two indicated projections.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelLimitToBase :
    pullback (overlapModelHom R f hij U a b) (c.π.app (op j)) ⟶
      pullback f (c.π.app (op i)) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst (U.f a) (U.f b) ≫ U.f a ≫
      pullback.fst f (Spec.map (R.map (homOfLE hij))))
    (pullback.snd _ _) (by
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc]
      change (pullback.fst _ _ ≫ overlapModelHom R f hij U a b) ≫
        Spec.map (R.map (homOfLE hij)) = _
      rw [pullback.condition, Category.assoc]
      congr 1
      simpa using c.w (homOfLE hij).op)

/-- The limit model map lies over the original stage overlap.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
lemma overlapModelLimitToBase_comp :
    overlapModelLimitToBase R c f hij U a b ≫ overlapLimitMap R c f hij =
      pullback.fst (overlapModelHom R f hij U a b) (c.π.app (op j)) ≫
        pullback.fst (U.f a) (U.f b) ≫ U.f a := by
  apply pullback.hom_ext
  · dsimp only [overlapModelLimitToBase, overlapLimitMap, baseChangeMap, pullback.map,
      Over.mk_hom, Over.homMk_left]
    simp only [Category.assoc, pullback.lift_fst,
      Category.comp_id]
  · dsimp only [overlapModelLimitToBase, overlapLimitMap, baseChangeMap, pullback.map,
      Over.mk_hom, Over.homMk_left]
    simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    simpa only [overlapModelHom, Category.assoc] using
      (pullback.condition (f := overlapModelHom R f hij U a b)
        (g := c.π.app (op j))).symm

/-- The map from the limit overlap model to either pulled-back chart.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelLimitChart (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (hr : r ≫ U.f d = pullback.fst (U.f a) (U.f b) ≫ U.f a) :
    pullback (overlapModelHom R f hij U a b) (c.π.app (op j)) ⟶
      (U.pullback₁ (overlapLimitMap R c f hij)).X d :=
  pullback.lift (overlapModelLimitToBase R c f hij U a b)
    (pullback.fst _ _ ≫ r) (by
      rw [Category.assoc, hr, overlapModelLimitToBase_comp])

/-- The canonical comparison on a chart of the limit overlap model.
Source: Stacks Project, Tags 01ZR (2) and 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapModelLimitComparison
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (hr : r ≫ U.f d = pullback.fst (U.f a) (U.f b) ≫ U.f a) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapModelLimitChart R c f hij U a b d r hr)).obj
      ((Scheme.Modules.pullback (U.pullbackHom (overlapLimitMap R c f hij) d)).obj
        (N d)) :=
  overlapDirectModelComparison
    (overlapLimitMap R c (overlapModelHom R f hij U a b) (le_refl j))
    (overlapModelChart R f hij U a b d r) (pullback.fst _ _ ≫ r)
    (overlapModelLimitChart R c f hij U a b d r hr)
    (U.pullbackHom (overlapLimitMap R c f hij) d) (by
        dsimp only [overlapLimitMap, overlapModelChart, baseChangeMap, pullback.map,
          Over.mk_hom, Over.homMk_left]
        simp only [← Category.assoc, pullback.lift_fst, Category.comp_id])
      (by exact pullback.lift_snd _ _ _) (N d)

/-- The conjugated transition on the limit of the fixed overlap model.
This is an explicit map, without choosing a witness of map descent.
Source: Stacks Project, Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapModelConjugate
    (N : (d : U.I₀) → (U.X d).Modules)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ d, (Scheme.Modules.pullback
      (U.pullbackHom (overlapLimitMap R c f hij) d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (overlapLimitMap R c f hij)).f d)).obj M) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
        (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
        (pullback.snd (U.f a) (U.f b)))).obj (N b)) := by
  let ra := pullback.fst (U.f a) (U.f b)
  let rb := pullback.snd (U.f a) (U.f b)
  let ha := overlapModelLimitChart R c f hij U a b a ra rfl
  let hb := overlapModelLimitChart R c f hij U a b b rb pullback.condition.symm
  let ta := overlapModelLimitComparison R c f hij U a b N a ra rfl
  let tb := overlapModelLimitComparison R c f hij U a b N b rb pullback.condition.symm
  exact overlapConjugatedTransition U (overlapLimitMap R c f hij) N M e a b
    (overlapModelLimitToBase R c f hij U a b) ha hb
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) _ _ ta tb


/-- The map from a stage overlap to the original overlap, by its two projections.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapPairToOriginal {k : I} (hjk : j ≤ k) :
    let V := U.pullback₁ (overlapStageMap R f hij hjk)
    pullback (V.f a) (V.f b) ⟶ pullback (U.f a) (U.f b) :=
  let q := overlapStageMap R f hij hjk
  let V := U.pullback₁ q
  pullback.lift
    (pullback.fst (V.f a) (V.f b) ≫ U.pullbackHom q a)
    (pullback.snd (V.f a) (V.f b) ≫ U.pullbackHom q b) (by
      rw [Category.assoc, Category.assoc, U.pullbackHom_map, U.pullbackHom_map,
        ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The map from a stage overlap to the base change of the original overlap.
Both projections are prescribed; no descent witness is selected.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapPairToModel {k : I} (hjk : j ≤ k) :
    let V := U.pullback₁ (overlapStageMap R f hij hjk)
    pullback (V.f a) (V.f b) ⟶
      pullback (overlapModelHom R f hij U a b) (Spec.map (R.map (homOfLE hjk))) :=
  let q := overlapStageMap R f hij hjk
  let V := U.pullback₁ q
  pullback.lift (overlapPairToOriginal R f hij U a b hjk)
    (pullback.fst (V.f a) (V.f b) ≫ V.f a ≫
      pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) (by
        dsimp only [overlapPairToOriginal, overlapModelHom]
        rw [pullback.lift_fst_assoc]
        simp only [Category.assoc, Scheme.Cover.pullbackHom_map_assoc]
        have hq : q ≫ pullback.snd f (Spec.map (R.map (homOfLE hij))) =
            pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk)))) ≫
              Spec.map (R.map (homOfLE hjk)) := by
          dsimp only [q, overlapStageMap, baseChangeMap, pullback.map]
          simpa only [Over.homMk_left, Over.mk_hom] using pullback.lift_snd _ _ _
        rw [hq])

/-- Compare the restriction of a stage overlap model module with the chart restriction.
Source: Stacks Project, Tags 01ZR (2), 0095 and 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapModelStageComparison {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (s : pullback ((U.pullback₁ (overlapStageMap R f hij hjk)).f a)
      ((U.pullback₁ (overlapStageMap R f hij hjk)).f b) ⟶
      (U.pullback₁ (overlapStageMap R f hij hjk)).X d)
    (hr : overlapPairToOriginal R f hij U a b hjk ≫ r =
      s ≫ U.pullbackHom (overlapStageMap R f hij hjk) d) :
    (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).obj
      ((Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d))) ≅
      (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback (U.pullbackHom (overlapStageMap R f hij hjk) d)).obj
          (N d)) :=
  overlapStageModelComparison (overlapPairToModel R f hij U a b hjk)
    (overlapStageMap R (overlapModelHom R f hij U a b) (le_refl j) hjk)
    (overlapModelChart R f hij U a b d r) s
    (U.pullbackHom (overlapStageMap R f hij hjk) d) (by
      have hq : overlapStageMap R (overlapModelHom R f hij U a b)
          (le_refl j) hjk ≫ pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE (le_refl j)))) =
          pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE hjk))) := by
        dsimp only [overlapStageMap, baseChangeMap, pullback.map]
        simpa only [Category.comp_id, Over.mk_hom] using pullback.lift_fst _ _ _
      dsimp only [overlapModelChart]
      calc
        _ = overlapPairToModel R f hij U a b hjk ≫
            pullback.fst (overlapModelHom R f hij U a b)
              (Spec.map (R.map (homOfLE hjk))) ≫ r := by
          simpa only [Category.assoc] using
            congrArg (fun z ↦ overlapPairToModel R f hij U a b hjk ≫ z ≫ r) hq
        _ = overlapPairToOriginal R f hij U a b hjk ≫ r := by
          rw [← Category.assoc]
          exact congrArg (fun z ↦ z ≫ r) (pullback.lift_fst _ _ _)
        _ = _ := hr) (N d)

/-- The first chart comparison, kept as a named construction to prevent expansion.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
@[irreducible]
def overlapModelStageComparisonFst {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules) :=
  let V := U.pullback₁ (overlapStageMap R f hij hjk)
  overlapModelStageComparison R f hij U a b hjk N a
    (pullback.fst (U.f a) (U.f b)) (pullback.fst (V.f a) (V.f b))
    (pullback.lift_fst _ _ _)

/-- The second chart comparison, kept as a named construction to prevent expansion.
Source: Stacks Project, Tags 0095 and 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
@[irreducible]
def overlapModelStageComparisonSnd {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules) :=
  let V := U.pullback₁ (overlapStageMap R f hij hjk)
  overlapModelStageComparison R f hij U a b hjk N b
    (pullback.snd (U.f a) (U.f b)) (pullback.snd (V.f a) (V.f b))
    (pullback.lift_snd _ _ _)

/-- An explicit map on the stage overlap, transported from a fixed-model map.
Source: Stacks Project, Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-pair-model-transport). -/
@[irreducible]
def overlapPairMapOfModel {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules)
    (α : (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
          (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
      (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
          (pullback.snd (U.f a) (U.f b)))).obj (N b))) :
    let q := overlapStageMap R f hij hjk
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b) :=
  (overlapModelStageComparisonFst R f hij U a b hjk N).inv ≫
    (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).map α ≫
    (overlapModelStageComparisonSnd R f hij U a b hjk N).hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local implicit_reducible] Precoverage.ZeroHypercover.pullback₁
  PreZeroHypercover.pullback₁ Scheme.Modules.pseudofunctor
  CategoryTheory.Pseudofunctor.comp CategoryTheory.PrelaxFunctor.comp
  CategoryTheory.Bicategory.Adj.forget₁ CategoryTheory.LocallyDiscrete.mkPseudofunctor
  CategoryTheory.PrelaxFunctorStruct.comp Prefunctor.comp
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete CategoryTheory.Adjunction.toCat
  overlapLimitMap overlapStageMap CategoryTheory.Pseudofunctor.toDescentData
  CategoryTheory.Pseudofunctor.DescentData.ofObj Quiver.Hom.toLoc

attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Adjunction.leftAdjointUniq
  Scheme.Modules.pullbackComp pullbackCompOfEq Scheme.Modules.pullbackCongr
  overlapDirectRestrictionIso overlapIteratedComparison
  CategoryTheory.Pseudofunctor.overlapPairBaseChangeHom limit.cone
  overlapPairSquare CategoryTheory.Pseudofunctor.overlapPairBaseChangeSquare

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false





private theorem overlap_model_restrictions_compose
    {X Y Z H₀ Hₖ Hlim : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M) (a b : U.I₀)
    (q₀ : Hₖ ⟶ H₀) (p₀ : Hlim ⟶ Hₖ) (t₀ : Hlim ⟶ H₀) (h₀ : p₀ ≫ q₀ = t₀)
    (r₀a : H₀ ⟶ U.X a) (r₀b : H₀ ⟶ U.X b)
    (d : pullback ((U.pullback₁ q).f a) ((U.pullback₁ q).f b) ⟶ Hₖ)
    (ha : Hlim ⟶ (U.pullback₁ t).X a) (hb : Hlim ⟶ (U.pullback₁ t).X b)
    (ν : Hlim ⟶ Z)
    (hνa : ha ≫ (U.pullback₁ t).f a = ν)
    (hνb : hb ≫ (U.pullback₁ t).f b = ν)
    (hka : (d ≫ q₀) ≫ r₀a = pullback.fst _ _ ≫ U.pullbackHom q a)
    (hkb : (d ≫ q₀) ≫ r₀b = pullback.snd _ _ ≫ U.pullbackHom q b)
    (ka : Hlim ⟶ U.X a) (kb : Hlim ⟶ U.X b)
    (hla : t₀ ≫ r₀a = ka) (hlb : t₀ ≫ r₀b = kb)
    (hda : ha ≫ U.pullbackHom t a = ka)
    (hdb : hb ≫ U.pullbackHom t b = kb)
    (z : pullback (((U.pullback₁ q).pullback₁ p).f a)
      (((U.pullback₁ q).pullback₁ p).f b) ⟶ Hlim)
    (hza : z ≫ ha = pullback.fst _ _ ≫ overlapIteratedChartHom U q p t h a)
    (hzb : z ≫ hb = pullback.snd _ _ ≫ overlapIteratedChartHom U q p t h b)
    (hz : z ≫ p₀ =
      pullback.lift
        (pullback.fst _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p a)
        (pullback.snd _ _ ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) p b) (by
          rw [Category.assoc, Category.assoc, Scheme.Cover.pullbackHom_map,
            Scheme.Cover.pullbackHom_map, ← Category.assoc, ← Category.assoc,
            pullback.condition]) ≫ d) :
    let F := (Scheme.Modules.pullback r₀a).obj (N a)
    let G := (Scheme.Modules.pullback r₀b).obj (N b)
    let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ h₀
    let canonicalτa := overlapDirectModelComparison t₀ r₀a ka ha
      (U.pullbackHom t a) hla hda (N a)
    let canonicalτb := overlapDirectModelComparison t₀ r₀b kb hb
      (U.pullbackHom t b) hlb hdb (N b)
    let canonicalsa := overlapStageModelComparison d q₀ r₀a
      (pullback.fst _ _) (U.pullbackHom q a) hka (N a)
    let canonicalsb := overlapStageModelComparison d q₀ r₀b
      (pullback.snd _ _) (U.pullbackHom q b) hkb (N b)
    ∀ (τa : (Scheme.Modules.tensorPullback t₀).obj F ≅
        (Scheme.Modules.pullback ha).obj
          ((Scheme.Modules.pullback (U.pullbackHom t a)).obj (N a)))
      (τb : (Scheme.Modules.tensorPullback t₀).obj G ≅
        (Scheme.Modules.pullback hb).obj
          ((Scheme.Modules.pullback (U.pullbackHom t b)).obj (N b)))
      (sa : (Scheme.Modules.pullback d).obj ((Scheme.Modules.tensorPullback q₀).obj F) ≅
        (Scheme.Modules.pullback
          (pullback.fst ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
          ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)))
      (sb : (Scheme.Modules.pullback d).obj ((Scheme.Modules.tensorPullback q₀).obj G) ≅
        (Scheme.Modules.pullback
          (pullback.snd ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
          ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b))),
      τa = canonicalτa → τb = canonicalτb → sa = canonicalsa → sb = canonicalsb →
    ∀ α : (Scheme.Modules.tensorPullback q₀).obj F ⟶
        (Scheme.Modules.tensorPullback q₀).obj G,
    ∀ θ : (Scheme.Modules.tensorPullback t₀).obj F ⟶
        (Scheme.Modules.tensorPullback t₀).obj G,
      θ = overlapConjugatedTransition U t N M e a b ν ha hb hνa hνb
        ((Scheme.Modules.tensorPullback t₀).obj F)
        ((Scheme.Modules.tensorPullback t₀).obj G) τa τb →
      σ.hom.app F ≫ (Scheme.Modules.tensorPullback p₀).map α = θ ≫ σ.hom.app G →
    ∀ φ : (Scheme.Modules.pullback
        (pullback.fst ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
        ((Scheme.Modules.pullback (U.pullbackHom q a)).obj (N a)) ⟶
      (Scheme.Modules.pullback
        (pullback.snd ((U.pullback₁ q).f a) ((U.pullback₁ q).f b))).obj
        ((Scheme.Modules.pullback (U.pullbackHom q b)).obj (N b)),
      φ = sa.inv ≫ (Scheme.Modules.pullback d).map α ≫ sb.hom →
      overlapPairSquare (U.pullback₁ q)
        (fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) p
        ((modulesPseudofunctor.toDescentData (((U.pullback₁ q).pullback₁ p).f)).obj M)
        (overlapIteratedComparison U q p t h N M e) a b φ := by
  dsimp only
  intro τa τb sa sb hτa hτb hsa hsb α θ hθ hα φ hφ
  apply overlap_conjugate_restriction_explicit U q p t h N M e a b ν ha hb hνa hνb
    z hza hzb _ _ τa τb θ hθ φ
  exact overlap_stage_model_restriction U q p t h N a b q₀ p₀ t₀ h₀ r₀a r₀b d ha hb
    hka hkb ka kb hla hlb hda hdb z hza hzb hz τa τb sa sb hτa hτb hsa hsb
    α θ hα φ hφ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A lifted map on the fixed overlap model gives the required pair square.
This is only transport of a given map at a given stage: it does not lift a map
or assert the existence of a later stage. No finiteness assumptions are needed.
Source: Stacks Project, Tag 01ZR (2), first proof, identification after restriction;
Tags 0095 and 0096, composition of inverse images.
(blueprint: lem-pc-overlap-pair-model-transport).

Proof: At stage k the universal overlap of the pulled-back charts is canonically
isomorphic to the base change of the fixed overlap. The isomorphism has first
projection given by the two chart projections to U_a and U_b, and second
projection given by the structure map to Spec R_k. Pull alpha across this
isomorphism and the pullback composition comparisons to obtain phi. Both the
stage and limit overlap identifications have these same prescribed projections,
so pullback uniqueness makes their square commute. Convert tensor pullback to
abstract pullback using the adjunction comparison. The canonical tensor
composition comparison is the conjugate of pushforward composition; associativity
of adjunction composition identifies it with the abstract pullback composition
comparison. Thus the assumed recovery equation, after pullback to the universal
limit overlap, is precisely the square for phi. In this equation the definition
of overlapModelConjugate cancels the comparison on the source and on the target;
the remaining component comparisons are overlapIteratedComparison. Empty
overlaps have their unique map and the same universal-property calculation. -/
theorem overlap_pair_square_of_model_recovery
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec))
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (N : (a : U.I₀) → (U.X a).Modules)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))).f a)).obj M)
    (a b : U.I₀)
    (k : I) (hjk : j ≤ k) :
    let g := overlapModelHom R f hij U a b
    let F := (Scheme.Modules.pullback (overlapModelChart R f hij U a b a
      (pullback.fst (U.f a) (U.f b)))).obj (N a)
    let G := (Scheme.Modules.pullback (overlapModelChart R f hij U a b b
      (pullback.snd (U.f a) (U.f b)))).obj (N b)
    let q₀ := overlapStageMap R g (le_refl j) hjk
    let p₀ := overlapLimitMap R c g ((le_refl j).trans hjk)
    let t₀ := overlapLimitMap R c g (le_refl j)
    let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ (by
      dsimp only [p₀, q₀, t₀, overlapLimitMap, overlapStageMap]
      rw [← baseChangeMap_comp]
      congr 1
      ext
      simpa using c.w (homOfLE hjk).op)
    ∀ α : (Scheme.Modules.tensorPullback q₀).obj F ⟶
        (Scheme.Modules.tensorPullback q₀).obj G,
      σ.hom.app F ≫ (Scheme.Modules.tensorPullback p₀).map α =
        overlapModelConjugate R c f hij U a b N M e ≫ σ.hom.app G →
      let q := overlapStageMap R f hij hjk
      let V := U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjk)
      let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
      let W := V.pullback₁ p
      let D := (modulesPseudofunctor.toDescentData W.f).obj M
      let ε := overlapIteratedComparison U q p (overlapLimitMap R c f hij)
        (by
          dsimp only [p, q, overlapLimitMap, overlapStageMap]
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op) N M e
      overlapPairSquare V A p D ε a b
        (overlapPairMapOfModel R f hij U a b hjk N α) := by
  dsimp only
  intro α hα
  let q := overlapStageMap R f hij hjk
  let p := overlapLimitMap R c f (hij.trans hjk)
  let t := overlapLimitMap R c f hij
  have h : p ≫ q = t := by
    dsimp only [p, q, t, overlapLimitMap, overlapStageMap]
    rw [← baseChangeMap_comp]
    congr 1
    ext
    simpa using c.w (homOfLE hjk).op
  let V : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
    U.pullback₁ q
  let W : (pullback f (c.π.app (op i))).OpenCover.{u} := V.pullback₁ p
  let g := overlapModelHom R f hij U a b
  let q₀ := overlapStageMap R g (le_refl j) hjk
  let p₀ := overlapLimitMap R c g ((le_refl j).trans hjk)
  let t₀ := overlapLimitMap R c g (le_refl j)
  have h₀ : p₀ ≫ q₀ = t₀ := by
    dsimp only [p₀, q₀, t₀, overlapLimitMap, overlapStageMap]
    rw [← baseChangeMap_comp]
    congr 1
    ext
    simpa using c.w (homOfLE hjk).op
  let ha := overlapModelLimitChart R c f hij U a b a
    (pullback.fst (U.f a) (U.f b)) rfl
  let hb := overlapModelLimitChart R c f hij U a b b
    (pullback.snd (U.f a) (U.f b)) pullback.condition.symm
  let va := pullback.fst (W.f a) (W.f b) ≫ overlapIteratedChartHom U q p t h a
  let vb := pullback.snd (W.f a) (W.f b) ≫ overlapIteratedChartHom U q p t h b
  have hva : overlapIteratedChartHom U q p t h a ≫ (U.pullback₁ t).f a = W.f a :=
    pullback.lift_fst _ _ _
  have hvb : overlapIteratedChartHom U q p t h b ≫ (U.pullback₁ t).f b = W.f b :=
    pullback.lift_fst _ _ _
  have hv : va ≫ (U.pullback₁ t).f a = vb ≫ (U.pullback₁ t).f b := by
    dsimp only [va, vb]
    rw [Category.assoc, hva, Category.assoc, hvb]
    exact pullback.condition (f := W.f a) (g := W.f b)
  let r : pullback (W.f a) (W.f b) ⟶ pullback (U.f a) (U.f b) :=
    pullback.lift (va ≫ U.pullbackHom t a) (vb ≫ U.pullbackHom t b) (by
      simpa only [Category.assoc, Scheme.Cover.pullbackHom_map] using
        congrArg (fun v ↦ v ≫ t) hv)
  let ν := va ≫ (U.pullback₁ t).f a
  have ht₁ : t ≫ pullback.fst f (Spec.map (R.map (homOfLE hij))) =
      pullback.fst f (c.π.app (op i)) := by
    dsimp only [t, overlapLimitMap, baseChangeMap, pullback.map]
    simp only [Over.mk_hom, Over.homMk_left, pullback.lift_fst, Category.comp_id]
  have ht₂ : t ≫ pullback.snd f (Spec.map (R.map (homOfLE hij))) =
      pullback.snd f (c.π.app (op i)) ≫ c.π.app (op j) := by
    dsimp only [t, overlapLimitMap, baseChangeMap, pullback.map]
    simp only [Over.mk_hom, Over.homMk_left, pullback.lift_snd]
  let z : pullback (W.f a) (W.f b) ⟶ pullback g (c.π.app (op j)) :=
    pullback.lift r (ν ≫ pullback.snd f (c.π.app (op i))) (by
      dsimp only [r, g, overlapModelHom, ν]
      simp only [pullback.lift_fst_assoc, Category.assoc,
        Scheme.Cover.pullbackHom_map_assoc]
      rw [ht₂]
      )
  have hzfst : z ≫ pullback.fst g (c.π.app (op j)) = r :=
    pullback.lift_fst _ _ _
  have hzsnd : z ≫ pullback.snd g (c.π.app (op j)) =
      ν ≫ pullback.snd f (c.π.app (op i)) := pullback.lift_snd _ _ _
  have hr₁ : r ≫ pullback.fst (U.f a) (U.f b) = va ≫ U.pullbackHom t a :=
    pullback.lift_fst _ _ _
  have hr₂ : r ≫ pullback.snd (U.f a) (U.f b) = vb ≫ U.pullbackHom t b :=
    pullback.lift_snd _ _ _
  have hzν : z ≫ overlapModelLimitToBase R c f hij U a b = ν := by
    apply pullback.hom_ext
    · have hbase : overlapModelLimitToBase R c f hij U a b ≫
          pullback.fst f (c.π.app (op i)) =
          pullback.fst g (c.π.app (op j)) ≫ pullback.fst (U.f a) (U.f b) ≫
            U.f a ≫ pullback.fst f (Spec.map (R.map (homOfLE hij))) :=
        pullback.lift_fst _ _ _
      rw [Category.assoc, hbase, ← Category.assoc z, hzfst,
        ← Category.assoc r, hr₁]
      dsimp only [ν]
      simp only [Category.assoc, Scheme.Cover.pullbackHom_map_assoc, ht₁]
    · change (z ≫ overlapModelLimitToBase R c f hij U a b) ≫
        pullback.snd f (c.π.app (op i)) = ν ≫ pullback.snd f (c.π.app (op i))
      have hbase : overlapModelLimitToBase R c f hij U a b ≫
          pullback.snd f (c.π.app (op i)) = pullback.snd g (c.π.app (op j)) :=
        pullback.lift_snd _ _ _
      rw [Category.assoc, hbase, hzsnd]
  have haf : ha ≫ (U.pullback₁ t).f a = overlapModelLimitToBase R c f hij U a b :=
    pullback.lift_fst _ _ _
  have hbf : hb ≫ (U.pullback₁ t).f b = overlapModelLimitToBase R c f hij U a b :=
    pullback.lift_fst _ _ _
  have had : ha ≫ U.pullbackHom t a =
      pullback.fst g (c.π.app (op j)) ≫ pullback.fst (U.f a) (U.f b) :=
    pullback.lift_snd _ _ _
  have hbd : hb ≫ U.pullbackHom t b =
      pullback.fst g (c.π.app (op j)) ≫ pullback.snd (U.f a) (U.f b) :=
    pullback.lift_snd _ _ _
  have hza : z ≫ ha = va := by
    apply pullback.hom_ext
    · change (z ≫ ha) ≫ (U.pullback₁ t).f a = va ≫ (U.pullback₁ t).f a
      rw [Category.assoc, haf, hzν]
    · change (z ≫ ha) ≫ U.pullbackHom t a = va ≫ U.pullbackHom t a
      rw [Category.assoc, had, ← Category.assoc, hzfst, hr₁]
  have hzb : z ≫ hb = vb := by
    apply pullback.hom_ext
    · change (z ≫ hb) ≫ (U.pullback₁ t).f b = vb ≫ (U.pullback₁ t).f b
      rw [Category.assoc, hbf, hzν]
      exact hv
    · change (z ≫ hb) ≫ U.pullbackHom t b = vb ≫ U.pullbackHom t b
      rw [Category.assoc, hbd, ← Category.assoc, hzfst, hr₂]
  let d := overlapPairToModel R f hij U a b hjk
  let r₀a := overlapModelChart R f hij U a b a (pullback.fst (U.f a) (U.f b))
  let r₀b := overlapModelChart R f hij U a b b (pullback.snd (U.f a) (U.f b))
  have hqfst : q₀ ≫ pullback.fst g (Spec.map (R.map (homOfLE (le_refl j)))) =
      pullback.fst g (Spec.map (R.map (homOfLE hjk))) := by
    dsimp only [q₀, overlapStageMap, baseChangeMap, pullback.map]
    simp only [Over.mk_hom, pullback.lift_fst, Category.comp_id]
  have hdfst : d ≫ pullback.fst g (Spec.map (R.map (homOfLE hjk))) =
      overlapPairToOriginal R f hij U a b hjk := pullback.lift_fst _ _ _
  have horg₁ : overlapPairToOriginal R f hij U a b hjk ≫
      pullback.fst (U.f a) (U.f b) =
      pullback.fst (V.f a) (V.f b) ≫ U.pullbackHom q a := pullback.lift_fst _ _ _
  have horg₂ : overlapPairToOriginal R f hij U a b hjk ≫
      pullback.snd (U.f a) (U.f b) =
      pullback.snd (V.f a) (V.f b) ≫ U.pullbackHom q b := pullback.lift_snd _ _ _
  have hka : (d ≫ q₀) ≫ r₀a = pullback.fst (V.f a) (V.f b) ≫ U.pullbackHom q a := by
    change (d ≫ q₀) ≫ (pullback.fst g (Spec.map (R.map (homOfLE (le_refl j)))) ≫
      pullback.fst (U.f a) (U.f b)) = _
    rw [← Category.assoc, Category.assoc d, hqfst, hdfst, horg₁]
  have hkb : (d ≫ q₀) ≫ r₀b = pullback.snd (V.f a) (V.f b) ≫ U.pullbackHom q b := by
    change (d ≫ q₀) ≫ (pullback.fst g (Spec.map (R.map (homOfLE (le_refl j)))) ≫
      pullback.snd (U.f a) (U.f b)) = _
    rw [← Category.assoc, Category.assoc d, hqfst, hdfst, horg₂]
  have hp₂ : p ≫ pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk)))) =
      pullback.snd f (c.π.app (op i)) ≫ c.π.app (op k) := by
    dsimp only [p, overlapLimitMap, baseChangeMap, pullback.map]
    simp only [Over.mk_hom, Over.homMk_left, pullback.lift_snd]
  have hν : ν = pullback.fst (W.f a) (W.f b) ≫ W.f a := by
    dsimp only [ν, va]
    rw [Category.assoc, hva]
  let l : pullback (W.f a) (W.f b) ⟶ pullback (V.f a) (V.f b) :=
    pullback.lift
      (pullback.fst (W.f a) (W.f b) ≫ V.pullbackHom p a)
      (pullback.snd (W.f a) (W.f b) ≫ V.pullbackHom p b) (by
        simpa only [Category.assoc, Scheme.Cover.pullbackHom_map] using
          congrArg (fun v ↦ v ≫ p) (pullback.condition (f := W.f a) (g := W.f b)))
  have hl₁ : l ≫ pullback.fst (V.f a) (V.f b) =
      pullback.fst (W.f a) (W.f b) ≫ V.pullbackHom p a := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd (V.f a) (V.f b) =
      pullback.snd (W.f a) (W.f b) ≫ V.pullbackHom p b := pullback.lift_snd _ _ _
  have hva_d : overlapIteratedChartHom U q p t h a ≫ U.pullbackHom t a =
      V.pullbackHom p a ≫ U.pullbackHom q a := pullback.lift_snd _ _ _
  have hvb_d : overlapIteratedChartHom U q p t h b ≫ U.pullbackHom t b =
      V.pullbackHom p b ≫ U.pullbackHom q b := pullback.lift_snd _ _ _
  have hro : r = l ≫ overlapPairToOriginal R f hij U a b hjk := by
    apply pullback.hom_ext
    · calc
        r ≫ pullback.fst (U.f a) (U.f b) = va ≫ U.pullbackHom t a := hr₁
        _ = pullback.fst (W.f a) (W.f b) ≫
            (V.pullbackHom p a ≫ U.pullbackHom q a) := by
          dsimp only [va]
          rw [Category.assoc, hva_d]
        _ = (l ≫ pullback.fst (V.f a) (V.f b)) ≫ U.pullbackHom q a := by
          simp only [hl₁, Category.assoc]
        _ = (l ≫ overlapPairToOriginal R f hij U a b hjk) ≫
            pullback.fst (U.f a) (U.f b) := by
          simp only [Category.assoc, horg₁]
    · calc
        r ≫ pullback.snd (U.f a) (U.f b) = vb ≫ U.pullbackHom t b := hr₂
        _ = pullback.snd (W.f a) (W.f b) ≫
            (V.pullbackHom p b ≫ U.pullbackHom q b) := by
          dsimp only [vb]
          rw [Category.assoc, hvb_d]
        _ = (l ≫ pullback.snd (V.f a) (V.f b)) ≫ U.pullbackHom q b := by
          simp only [hl₂, Category.assoc]
        _ = (l ≫ overlapPairToOriginal R f hij U a b hjk) ≫
            pullback.snd (U.f a) (U.f b) := by
          simp only [Category.assoc, horg₂]
  have hp₀fst : p₀ ≫ pullback.fst g (Spec.map (R.map (homOfLE hjk))) =
      pullback.fst g (c.π.app (op j)) := by
    dsimp only [p₀, overlapLimitMap, baseChangeMap, pullback.map]
    simp only [Over.mk_hom, Over.homMk_left, pullback.lift_fst, Category.comp_id]
  have hp₀snd : p₀ ≫ pullback.snd g (Spec.map (R.map (homOfLE hjk))) =
      pullback.snd g (c.π.app (op j)) ≫ c.π.app (op k) := by
    dsimp only [p₀, overlapLimitMap, baseChangeMap, pullback.map]
    simp only [Over.mk_hom, Over.homMk_left, pullback.lift_snd]
  have hdsnd : d ≫ pullback.snd g (Spec.map (R.map (homOfLE hjk))) =
      pullback.fst (V.f a) (V.f b) ≫ V.f a ≫
        pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk)))) :=
    pullback.lift_snd _ _ _
  have hz : z ≫ p₀ = l ≫ d := by
    apply pullback.hom_ext
    · change (z ≫ p₀) ≫ pullback.fst g (Spec.map (R.map (homOfLE hjk))) =
        (l ≫ d) ≫ pullback.fst g (Spec.map (R.map (homOfLE hjk)))
      simp only [Category.assoc, hp₀fst, hdfst]
      rw [hzfst, hro]
    · change (z ≫ p₀) ≫ pullback.snd g (Spec.map (R.map (homOfLE hjk))) =
        (l ≫ d) ≫ pullback.snd g (Spec.map (R.map (homOfLE hjk)))
      simp only [Category.assoc, hp₀snd, hdsnd]
      rw [← Category.assoc z, hzsnd, ← Category.assoc l, hl₁, hν]
      simp only [Category.assoc, Scheme.Cover.pullbackHom_map_assoc, hp₂]
      rfl
  have ht₀fst : t₀ ≫ pullback.fst g (Spec.map (R.map (homOfLE (le_refl j)))) =
      pullback.fst g (c.π.app (op j)) := by
    dsimp only [t₀, overlapLimitMap, baseChangeMap, pullback.map]
    simp only [Over.mk_hom, Over.homMk_left, pullback.lift_fst, Category.comp_id]
  have hla : t₀ ≫ r₀a =
      pullback.fst g (c.π.app (op j)) ≫ pullback.fst (U.f a) (U.f b) := by
    change t₀ ≫ (pullback.fst g (Spec.map (R.map (homOfLE (le_refl j)))) ≫
      pullback.fst (U.f a) (U.f b)) = _
    rw [← Category.assoc, ht₀fst]
  have hlb : t₀ ≫ r₀b =
      pullback.fst g (c.π.app (op j)) ≫ pullback.snd (U.f a) (U.f b) := by
    change t₀ ≫ (pullback.fst g (Spec.map (R.map (homOfLE (le_refl j)))) ≫
      pullback.snd (U.f a) (U.f b)) = _
    rw [← Category.assoc, ht₀fst]
  let τa := overlapModelLimitComparison R c f hij U a b N a
    (pullback.fst (U.f a) (U.f b)) rfl
  let τb := overlapModelLimitComparison R c f hij U a b N b
    (pullback.snd (U.f a) (U.f b)) pullback.condition.symm
  let sa := overlapModelStageComparisonFst R f hij U a b hjk N
  let sb := overlapModelStageComparisonSnd R f hij U a b hjk N
  have hτa := overlapModelLimitComparison.eq_def R c f hij U a b N a
    (pullback.fst (U.f a) (U.f b)) rfl
  have hτb := overlapModelLimitComparison.eq_def R c f hij U a b N b
    (pullback.snd (U.f a) (U.f b)) pullback.condition.symm
  have hsa₀ := overlapModelStageComparison.eq_def R f hij U a b hjk N a
    (pullback.fst (U.f a) (U.f b)) (pullback.fst (V.f a) (V.f b))
    (pullback.lift_fst _ _ _)
  have hsb₀ := overlapModelStageComparison.eq_def R f hij U a b hjk N b
    (pullback.snd (U.f a) (U.f b)) (pullback.snd (V.f a) (V.f b))
    (pullback.lift_snd _ _ _)
  have hsa := (overlapModelStageComparisonFst.eq_def R f hij U a b hjk N).trans hsa₀
  have hsb := (overlapModelStageComparisonSnd.eq_def R f hij U a b hjk N).trans hsb₀
  have hφ := overlapPairMapOfModel.eq_def R f hij U a b hjk N α
  exact overlap_model_restrictions_compose U q p t h N M e a b q₀ p₀ t₀ h₀
    r₀a r₀b d ha hb (overlapModelLimitToBase R c f hij U a b) haf hbf
    hka hkb (pullback.fst g (c.π.app (op j)) ≫ pullback.fst (U.f a) (U.f b))
    (pullback.fst g (c.π.app (op j)) ≫ pullback.snd (U.f a) (U.f b))
    hla hlb had hbd z hza hzb hz τa τb sa sb hτa hτb hsa hsb
    α (overlapModelConjugate R c f hij U a b N M e) rfl hα
    (overlapPairMapOfModel R f hij U a b hjk N α) hφ

end
end AlgebraicGeometry
