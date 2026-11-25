/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Finite bases for the Picard base-change stalks

Source: Stacks Project, Tags 0BDP, 01C6 and 0097.
(blueprint: lem-sc-picard-base-change-stalk-finite-bases).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

namespace Modules

-- The coordinate-germ construction below is adapted from the proved private helpers in
-- WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank. That module
-- exports only a finrank equality, which does not by itself supply the basis needed here.

/-- Coordinate germs on neighbourhoods intersected with the trivializing open. -/
private noncomputable def coordinateCocone {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens)
    (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Cocone ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of (X.presheaf.stalk x)
  ι :=
    { app := fun V ↦ AddCommGrpCat.ofHom
        (((X.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hx⟩).hom.toAddMonoidHom).comp
          (((π.val.app (Opposite.op (Over.mk
            (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U)))).hom.toAddMonoidHom).comp
            (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op).hom))
      naturality := by
        intro V W f
        ext m
        let a : W.unop.1 ⊓ U ⟶ V.unop.1 ⊓ U := homOfLE (inf_le_inf f.unop.le le_rfl)
        let a' : Over.mk (homOfLE inf_le_right : W.unop.1 ⊓ U ⟶ U) ⟶
            Over.mk (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U) := Over.homMk a
        have hπ := ConcreteCategory.congr_hom (π.val.naturality a'.op)
          (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op m)
        change X.presheaf.germ (W.unop.1 ⊓ U) x ⟨W.unop.2, hx⟩
          ((π.val.app (Opposite.op (Over.mk (homOfLE inf_le_right : W.unop.1 ⊓ U ⟶ U)))).hom
            (M.presheaf.map (homOfLE inf_le_left : W.unop.1 ⊓ U ⟶ W.unop.1).op
              (M.presheaf.map (homOfLE f.unop.le : W.unop.1 ⟶ V.unop.1).op m))) =
          X.presheaf.germ (V.unop.1 ⊓ U) x ⟨V.unop.2, hx⟩
            ((π.val.app (Opposite.op (Over.mk (homOfLE inf_le_right : V.unop.1 ⊓ U ⟶ U)))).hom
              (M.presheaf.map (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op m))
        rw [← M.presheaf.map_comp_apply]
        have hw : (homOfLE f.unop.le : W.unop.1 ⟶ V.unop.1).op ≫
            (homOfLE inf_le_left : W.unop.1 ⊓ U ⟶ W.unop.1).op =
            (homOfLE inf_le_left : V.unop.1 ⊓ U ⟶ V.unop.1).op ≫ a.op :=
          Subsingleton.elim _ _
        rw [hw, M.presheaf.map_comp_apply]
        rw [← X.presheaf.germ_res_apply a x ⟨W.unop.2, hx⟩]
        congr 1 }

/-- The additive map on stalks determined by local coordinate germs. -/
private noncomputable def coordinateAdd {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx :
    x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →+ X.presheaf.stalk x :=
  (colimit.desc _ (coordinateCocone M x U hx π)).hom

/-- The coordinate cocone computes its stalk map on a representative germ. -/
private lemma coordinateAdd_germ {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (m : Γ(M, V)) :
    coordinateAdd M x U hx π (M.presheaf.germ V x hxV m) =
      X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩
        ((π.val.app (Opposite.op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom
          (M.presheaf.map (homOfLE inf_le_left : V ⊓ U ⟶ V).op m)) := by
  change (colimit.ι _ (Opposite.op (⟨V, hxV⟩ : TopologicalSpace.OpenNhds x)) ≫
    colimit.desc _ (coordinateCocone M x U hx π)) m = _
  rw [colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate germs respect the action of the structure-ring stalk. -/
private noncomputable def coordinateLinear {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens)
    (hx : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  stalkLinearMapMk (coordinateAdd M x U hx π) fun V hxV r m ↦ by
    rw [coordinateAdd_germ, coordinateAdd_germ, Scheme.Modules.map_smul]
    rw [(π.val.app _).hom.map_smul]
    change X.presheaf.germ (V ⊓ U) x ⟨hxV, hx⟩ (_ * _) = _
    rw [map_mul, X.presheaf.germ_res_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Within the trivializing open, coordinates can be computed without intersecting. -/
private lemma coordinateLinear_germ_of_le {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx
    : x ∈ U)
    (π : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U) (m : Γ(M, V)) :
    coordinateLinear M x U hx π (M.presheaf.germ V x hxV m) =
      X.presheaf.germ V x hxV
        ((π.val.app (Opposite.op (Over.mk (homOfLE hVU)))).hom m) := by
  change coordinateAdd M x U hx π (M.presheaf.germ V x hxV m) = _
  rw [coordinateAdd_germ]
  let a : V ⊓ U ⟶ V := homOfLE inf_le_left
  let a' : Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U) ⟶
      Over.mk (homOfLE hVU : V ⟶ U) := Over.homMk a
  have hπ := ConcreteCategory.congr_hom (π.val.naturality a'.op) m
  have he : (π.val.app (Opposite.op (Over.mk (homOfLE inf_le_right : V ⊓ U ⟶ U)))).hom
      (M.presheaf.map a.op m) =
      X.presheaf.map a.op ((π.val.app (Opposite.op (Over.mk (homOfLE hVU)))).hom m) :=
    hπ
  rw [he, X.presheaf.germ_res_apply]

/-- A coordinate projection in the chosen local trivialization. -/
private noncomputable def localProjection {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) {I : Type
    u} [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.hom ≫ SheafOfModules.freeπ j

/-- A coordinate inclusion in the chosen local trivialization. -/
private noncomputable def localInclusion {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  SheafOfModules.ιFree j ≫ e.inv

/-- The germ of a local coordinate vector. -/
private noncomputable def localBasisGerm {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx
    : x ∈ U) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I) : M.presheaf.stalk x :=
  M.presheaf.germ U x hx
    ((localInclusion M U e j).val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U)))

set_option backward.isDefEq.respectTransparency false in
/-- Local coordinate vectors give the same germ after restriction. -/
private lemma localBasisGerm_eq {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) (j : I)
    (V : X.Opens) (hxV : x ∈ V) (hVU : V ≤ U) :
    localBasisGerm M x U hx e j = M.presheaf.germ V x hxV
      ((localInclusion M U e j).val.app (Opposite.op (Over.mk (homOfLE hVU))) (1 : Γ(X, V))) := by
  let a' : Over.mk (homOfLE hVU : V ⟶ U) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE hVU)
  have he := ConcreteCategory.congr_hom
    ((localInclusion M U e j).val.naturality a'.op) (1 : Γ(X, U))
  change localBasisGerm M x U hx e j = _
  unfold localBasisGerm
  rw [← M.presheaf.germ_res_apply (homOfLE hVU) x hxV]
  congr 1
  change (localInclusion M U e j).val.app (Opposite.op (Over.mk (homOfLE hVU)))
      (X.presheaf.map (homOfLE hVU).op (1 : Γ(X, U))) =
    M.presheaf.map (homOfLE hVU).op
      ((localInclusion M U e j).val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at he
  rw [map_one] at he
  exact he.symm

/-- The sum of the coordinate projection-inclusion composites is the identity. -/
private lemma local_sum {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) {I : Type u} [Fintype I]
    [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) :
    ∑ j, localProjection M U e j ≫ localInclusion M U e j = 𝟙 (M.over U) := by
  simp only [localProjection, localInclusion, Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp, SheafOfModules.sum_freeπ_ιFree,
    Category.id_comp, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk coordinate vectors have Kronecker-delta coordinates. -/
private lemma coordinate_basis {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    {I : Type u} [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (j k : I) :
    coordinateLinear M x U hx (localProjection M U e j)
      (localBasisGerm M x U hx e k) = if k = j then 1 else 0 := by
  unfold localBasisGerm
  rw [coordinateLinear_germ_of_le M x U hx _ U hx le_rfl]
  have hp : localInclusion M U e k ≫ localProjection M U e j =
      if k = j then 𝟙 _ else 0 := by
    simp only [localInclusion, localProjection, Category.assoc, Iso.inv_hom_id_assoc,
      SheafOfModules.ιFree_freeπ]
  have he := congrArg (fun g ↦
    (g.val.app (Opposite.op (Over.mk (𝟙 U)))).hom (1 : Γ(X, U))) hp
  change (localProjection M U e j).val.app (Opposite.op (Over.mk (𝟙 U)))
      ((localInclusion M U e k).val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U))) =
    _ at he
  change X.presheaf.germ U x hx
    ((localProjection M U e j).val.app (Opposite.op (Over.mk (𝟙 U)))
      ((localInclusion M U e k).val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U)))) = _
  split_ifs at he ⊢ with h
  · change (localProjection M U e j).val.app (Opposite.op (Over.mk (𝟙 U)))
        ((localInclusion M U e k).val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (1 : Γ(X,
            U)) at he
    exact (congrArg (fun a : Γ(X, U) ↦ X.presheaf.germ U x hx a) he).trans (map_one _)
  · change (localProjection M U e j).val.app (Opposite.op (Over.mk (𝟙 U)))
        ((localInclusion M U e k).val.app (Opposite.op (Over.mk (𝟙 U))) (1 : Γ(X, U))) = (0 : Γ(X,
            U)) at he
    exact (congrArg (fun a : Γ(X, U) ↦ X.presheaf.germ U x hx a) he).trans (map_zero _)

set_option backward.isDefEq.respectTransparency false in
/-- Every germ is the sum of its coordinates times the local basis germs. -/
private lemma sum_coordinate_basis {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈
    U) {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) (m : M.presheaf.stalk x) :
    ∑ j, coordinateLinear M x U hx (localProjection M U e j) m •
      localBasisGerm M x U hx e j = m := by
  obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hx
  simp_rw [coordinateLinear_germ_of_le M x U hx _ V hxV hVU,
    localBasisGerm_eq M x U hx e _ V hxV hVU, ← Scheme.Modules.germ_smul]
  rw [← map_sum]
  congr 1
  have he := congrArg (fun g ↦
    (g.val.app (Opposite.op (Over.mk (homOfLE hVU)))).hom m) (local_sum M U e)
  rw [SheafOfModules.sum_val_app_apply] at he
  change ∑ j, (localInclusion M U e j).val.app (Opposite.op (Over.mk (homOfLE hVU)))
      ((localProjection M U e j).val.app (Opposite.op (Over.mk (homOfLE hVU))) m) = m at he
  calc
    _ = ∑ j, (localInclusion M U e j).val.app (Opposite.op (Over.mk (homOfLE hVU)))
        ((localProjection M U e j).val.app (Opposite.op (Over.mk (homOfLE hVU))) m) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← ((localInclusion M U e j).val.app _).hom.map_smul]
      congr 1
      exact mul_one (show Γ(X, V) from
        (localProjection M U e j).val.app (Opposite.op (Over.mk (homOfLE hVU))) m)
    _ = m := he

/-- A finite local trivialization induces an explicit linear equivalence on stalks. -/
private noncomputable def localStalkEquiv {X : Scheme.{u}} (M : X.Modules) (x : X) (U : X.Opens) (hx
    : x ∈ U) {I : Type u} [Fintype I] [DecidableEq I]
    (e : M.over U ≅ SheafOfModules.free I) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (I → X.presheaf.stalk x) :=
  LinearEquiv.ofBijective (LinearMap.pi fun j ↦
    coordinateLinear M x U hx (localProjection M U e j)) (by
    constructor
    · intro m n h
      rw [← sum_coordinate_basis M x U hx e m, ← sum_coordinate_basis M x U hx e n]
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg (fun a ↦ a • localBasisGerm M x U hx e j) (congrFun h j)
    · intro c
      refine ⟨∑ j, c j • localBasisGerm M x U hx e j, ?_⟩
      ext k
      change coordinateLinear M x U hx (localProjection M U e k) _ = c k
      rw [map_sum]
      simp_rw [LinearMap.map_smul, coordinate_basis]
      simp)

/-- The local coordinate construction also supplies a finite basis, without a fixed rank. -/
private theorem finiteLocallyFree_stalk_basis {X : Scheme.{u}} (M : X.Modules)
    [M.IsFiniteLocallyFree] (x : X) :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (M.presheaf.stalk x)) := by
  classical
  obtain ⟨U, I, hI, hx, e⟩ := exists_mem_over_iso_free M x
  let := hI
  obtain ⟨e⟩ := e
  let E := localStalkEquiv M x U hx e
  exact ⟨Fintype.card I,
    ⟨((Pi.basisFun (X.presheaf.stalk x) I).map E.symm).reindex (Fintype.equivFin I)⟩⟩

end Modules

private noncomputable def tensorComparison {A B : Scheme.{u}} (h : A ⟶ B) :
    Modules.tensorPullback h ≅ Modules.pullback h :=
  (Modules.nonempty_tensorPullbackAdjunction h).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction h)

/-- Local rank witnesses give global finite local freeness for either direct image. -/
private theorem rankMatch_directImage_finiteLocallyFree {X S T : Scheme.{u}}
    (f : X ⟶ S) (E : X.Modules) (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) {T' : Scheme.{u}} (h : T' ⟶ T)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) :
    ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
      ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F)).IsFiniteLocallyFree := by
  classical
  let N := (Modules.pushforward (pullback.snd f (h ≫ g))).obj
    ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F)
  have hlocal (t : T') : ∃ U : T'.Opens, t ∈ U ∧
      ((Modules.tensorPullback U.ι).obj N).IsFiniteLocallyFree := by
    obtain ⟨U, ht, r, hE, hD, _⟩ := hR h t
    have hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj N) r := by
      rcases hF with rfl | rfl
      · exact hE
      · exact hD
    have := hr
    exact ⟨U, ht, SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} _ r⟩
  choose U ht hU using hlocal
  apply Modules.isFiniteLocallyFree_of_isOpenImmersion N (fun t ↦ (U t).ι)
  · apply eq_top_iff.mpr
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, by
      rw [Scheme.Opens.opensRange_ι]
      exact ht t⟩
  · intro t
    have := hU t
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
      ((tensorComparison (U t).ι).app N)

/-- Associativity transports the iterated direct image to the composite base change. -/
private noncomputable def iteratedDirectImageIso {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) (F : X.Modules) :
    (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
        ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj
          ((Modules.tensorPullback (pullback.fst f g)).obj F)) ≅
      (Modules.pushforward (pullback.snd f (h ≫ g))).obj
        ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F) := by
  let e := pullbackLeftPullbackSndIso f g h
  let q := pullback.fst f (h ≫ g)
  let p := pullback.snd f (h ≫ g)
  let v := pullback.fst (pullback.snd f g) h
  let q₀ := pullback.fst f g
  let p' := pullback.snd (pullback.snd f g) h
  have hq : e.hom ≫ q = v ≫ q₀ := pullbackLeftPullbackSndIso_hom_fst f g h
  have hp : e.hom ≫ p = p' := pullbackLeftPullbackSndIso_hom_snd f g h
  let a : (Modules.tensorPullback v).obj ((Modules.tensorPullback q₀).obj F) ≅
      (Modules.tensorPullback e.hom).obj ((Modules.tensorPullback q).obj F) :=
    ((Modules.nonempty_tensorPullbackComp v q₀).some.app F).symm ≪≫
      (eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj F) hq)).symm ≪≫
      (Modules.nonempty_tensorPullbackComp e.hom q).some.app F
  let eqv : (pullback (pullback.snd f g) h).Modules ≌
      (pullback f (h ≫ g)).Modules :=
    CategoryTheory.Equivalence.mk (Modules.pushforward e.hom) (Modules.pushforward e.inv)
      (Modules.pushforwardComp e.hom e.inv ≪≫
        Modules.pushforwardCongr e.hom_inv_id ≪≫ Modules.pushforwardId _).symm
      (Modules.pushforwardComp e.inv e.hom ≪≫
        Modules.pushforwardCongr e.inv_hom_id ≪≫ Modules.pushforwardId _)
  have : (Modules.pushforward e.hom).IsEquivalence := eqv.isEquivalence_functor
  let adj := (Modules.nonempty_tensorPullbackAdjunction e.hom).some
  have : IsIso adj.unit := inferInstance
  exact (Modules.pushforward p').mapIso a ≪≫
    (Modules.pushforwardCongr hp).symm.app _ ≪≫
    (Modules.pushforwardComp e.hom p).symm.app _ ≪≫
    (Modules.pushforward p).mapIso (asIso (adj.unit.app _)).symm

/-- The source and target stalks are finite free, without comparing their ranks.
Source: Stacks Project, Tags 01C6 and 0098; the local frames in the rank reduction
of Tag 0BDP. This is the finite-freeness part of the original stalk-rank argument.

Proof: apply hR to the identity of T at h(t). Use the identity law on morphisms
and choose a trivializing open inside the resulting neighbourhood for the direct
image of E, or for that of its dual according to hF. Taking germs of the frame
and its coordinate projections gives a finite basis at h(t). The pullback stalk
formula identifies P_t with extension of scalars of this module along h's stalk
map; tensoring its basis gives a finite basis of P_t.
For Q, apply hR to h at t. The associativity isomorphism between the iterated
fibre product and X times_S T', together with composition of tensor pullbacks,
identifies the iterated pulled-back F with the pullback of F along the composite
base change. Pushforward along this isomorphism identifies Q with the direct
image occurring in hR. Choose a trivializing open inside the resulting
neighbourhood and take germs of its frame to obtain a finite basis of Q_t.
The two bases can have unrelated cardinalities at this stage. No proper-image
or fibre-rank comparison is needed. A zero-rank frame gives an empty basis;
there is no point t when T' is empty.
(blueprint: lem-sc-picard-base-change-stalk-finite-bases) -/
theorem picardRankMatch_baseChange_stalk_finite_bases {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) {T' : Scheme.{u}} (h : T' ⟶ T)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) (t : T') :
    let P := (Modules.tensorPullback h).obj
      ((Modules.pushforward (pullback.snd f g)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    let Q := (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
      ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    (∃ r : ℕ, Nonempty (Module.Basis (Fin r) (T'.presheaf.stalk t)
      (P.presheaf.stalk t))) ∧
    (∃ s : ℕ, Nonempty (Module.Basis (Fin s) (T'.presheaf.stalk t)
      (Q.presheaf.stalk t))) := by
  let N := (Modules.pushforward (pullback.snd f g)).obj
    ((Modules.tensorPullback (pullback.fst f g)).obj F)
  have hN : N.IsFiniteLocallyFree := by
    exact (congrArg (fun k : T ⟶ S ↦
      ((Modules.pushforward (pullback.snd f k)).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj F)).IsFiniteLocallyFree)
      (Category.id_comp g)).mp
        (rankMatch_directImage_finiteLocallyFree f E g hR (𝟙 T) F hF)
  have hP := SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
    ((tensorComparison h).app N).symm
  have hC := rankMatch_directImage_finiteLocallyFree f E g hR h F hF
  have hQ := SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
    (iteratedDirectImageIso f g h F).symm
  exact ⟨Modules.finiteLocallyFree_stalk_basis _ t,
    Modules.finiteLocallyFree_stalk_basis _ t⟩

end AlgebraicGeometry.Scheme
