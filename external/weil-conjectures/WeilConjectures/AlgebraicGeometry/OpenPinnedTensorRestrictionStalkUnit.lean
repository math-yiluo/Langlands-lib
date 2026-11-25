/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # Open restriction compatibility of the tensor pullback unit

Source: Stacks Project, Tags 0096 and 0098.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry

section

private theorem open_normal (X : Scheme.{u}) (U : X.Opens) :
    (openPinnedTensorOpenIso X U).hom ≫ (Scheme.Modules.overFunctorEquiv U).hom =
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
        (Scheme.Modules.restrictAdjunction U.ι)).hom := by
  simp only [openPinnedTensorOpenIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ ≫
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).leftAdjointUniq
      (Scheme.Modules.restrictAdjunction U.ι)).hom = _
  exact Adjunction.leftAdjointUniq_trans _ _ _

-- These APIs keep open-immersion constructions abstract during elaboration.
private theorem restrict_image_unit
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
    (M : X.Modules) (W : Y.Opens) :
    let A := i ''ᵁ W
    let t : W ⟶ i ⁻¹ᵁ A := homOfLE (by rintro y hy; exact ⟨y, hy, rfl⟩)
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction i).unit.app M) A ≫
      ((Scheme.Modules.restrictFunctor i).obj M).presheaf.map t.op =
        𝟙 (M.presheaf.obj (op A)) := by
  dsimp only
  let A := i ''ᵁ W
  let t : W ⟶ i ⁻¹ᵁ A := homOfLE (by rintro y hy; exact ⟨y, hy, rfl⟩)
  simp only [Scheme.Modules.restrictAdjunction_unit_app_app]
  conv_lhs => arg 2; rw [Scheme.Modules.restrict_map M i t]
  rw [← M.presheaf.map_comp]
  have h : (homOfLE (i.image_preimage_le A)).op ≫
      (i.opensFunctor.map t).op = 𝟙 (op A) := Subsingleton.elim _ _
  rw [h]
  exact M.presheaf.map_id _

private theorem restriction_pushforward_transport
    {X X' Y Y' : Scheme.{u}} (k : X' ⟶ X)
    (i : Y ⟶ X) (o : Y' ⟶ X') (j : Y' ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion o]
    (hj : j ≫ i = o ≫ k) (W : Y.Opens) (Q : X'.Modules) :
    let A := i ''ᵁ W
    let RQ := (Scheme.Modules.restrictFunctor o).obj Q
    let t : W ⟶ i ⁻¹ᵁ A := homOfLE (by rintro y hy; exact ⟨y, hy, rfl⟩)
    let jt := (Opens.map j.base).map t
    let hW : o ''ᵁ (j ⁻¹ᵁ W) ≤ k ⁻¹ᵁ A := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨j y, hy, congrArg (fun q : Y' ⟶ X ↦ q y) hj⟩
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction o).unit.app Q) (k ⁻¹ᵁ A) ≫
      Scheme.Modules.Hom.app
        ((Scheme.Modules.pushforwardComp o k ≪≫ Scheme.Modules.pushforwardCongr rfl).hom.app
          RQ) A ≫
      Scheme.Modules.Hom.app
        ((Scheme.Modules.pushforwardComp j i ≪≫ Scheme.Modules.pushforwardCongr hj).inv.app
          RQ) A ≫ RQ.presheaf.map jt.op = Q.presheaf.map (homOfLE hW).op := by
  dsimp only
  simp only [Scheme.Modules.restrictAdjunction_unit_app_app,
    Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app, Category.assoc]
  have hm {B C : Y'.Opens} (q : B ⟶ C) :
      ((Scheme.Modules.restrictFunctor o).obj Q).presheaf.map q.op =
        Q.presheaf.map (o.opensFunctor.map q).op := Scheme.Modules.restrict_map Q o q
  conv_lhs => arg 2; erw [Category.id_comp]
  conv_lhs => arg 2; arg 1; rw [hm]
  conv_lhs => arg 2; arg 2; arg 1; rw [hm]
  conv_lhs => arg 2; arg 2; arg 2; erw [Category.id_comp]; rw [hm]
  conv_lhs => arg 2; arg 2; rw [← Q.presheaf.map_comp]
  conv_lhs => arg 2; rw [← Q.presheaf.map_comp]
  rw [← Q.presheaf.map_comp]
  apply congrArg Q.presheaf.map
  exact Subsingleton.elim _ _

-- Section transport uses the restriction API rather than unfolding its sheaf data.
-- Work with abstract left adjoints when taking section components of the mate identity.
private theorem unit_sections_of_conjugate
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (Lk : X.Modules ⥤ X'.Modules) (Lj : U.toScheme.Modules ⥤ U'.toScheme.Modules)
    (ak : Lk ⊣ Scheme.Modules.pushforward k)
    (aj : Lj ⊣ Scheme.Modules.pushforward j)
    (E : Scheme.Modules.restrictFunctor U.ι ⋙ Lj ⟶
      Lk ⋙ Scheme.Modules.restrictFunctor U'.ι)
    (hE : conjugateEquiv (ak.comp (Scheme.Modules.restrictAdjunction U'.ι))
        ((Scheme.Modules.restrictAdjunction U.ι).comp aj) E =
      (Scheme.Modules.pushforwardComp U'.ι k ≪≫ Scheme.Modules.pushforwardCongr rfl).hom ≫
        (Scheme.Modules.pushforwardComp j U.ι ≪≫ Scheme.Modules.pushforwardCongr hj).inv)
    (M : X.Modules) (N : U.toScheme.Modules)
    (r : N ⟶ (Scheme.Modules.restrictFunctor U.ι).obj M) (W : U.toScheme.Opens) :
    let hW : U'.ι ''ᵁ (j ⁻¹ᵁ W) ≤ k ⁻¹ᵁ (U.ι ''ᵁ W) := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨j y, hy, congrArg (fun q : U'.toScheme ⟶ X ↦ q y) hj⟩
    Scheme.Modules.Hom.app (aj.unit.app N) W ≫
        Scheme.Modules.Hom.app (Lj.map r ≫ E.app M) (j ⁻¹ᵁ W) =
      Scheme.Modules.Hom.app r W ≫ Scheme.Modules.Hom.app (ak.unit.app M) (U.ι ''ᵁ W) ≫
        (Lk.obj M).presheaf.map (homOfLE hW).op := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let bi := Scheme.Modules.restrictAdjunction U.ι
  let bo := Scheme.Modules.restrictAdjunction U'.ι
  let qs := Scheme.Modules.pushforwardComp j U.ι ≪≫ Scheme.Modules.pushforwardCongr hj
  let qt := Scheme.Modules.pushforwardComp U'.ι k ≪≫ Scheme.Modules.pushforwardCongr rfl
  let T := Lk.obj M
  have hu := unit_conjugateEquiv (ak.comp bo) (bi.comp aj) E M
  rw [hE] at hu
  let A := U.ι ''ᵁ W
  let R : U.toScheme.Modules := (Scheme.Modules.restrictFunctor U.ι).obj M
  let S : U'.toScheme.Modules := (Scheme.Modules.restrictFunctor U'.ι).obj T
  let t : W ⟶ U.ι ⁻¹ᵁ A := homOfLE (by
    rintro y hy
    exact ⟨y, hy, rfl⟩)
  let jt := (Opens.map j.base).map t
  have hv := congrArg (fun q ↦ Scheme.Modules.Hom.app q A ≫ S.presheaf.map jt.op) hu
  simp only [Adjunction.comp_unit_app, Functor.comp_map, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Category.assoc] at hv
  have hnE := (Scheme.Modules.Hom.mapPresheaf (E.app M)).naturality jt.op
  change (Lj.obj R).presheaf.map jt.op ≫
      Scheme.Modules.Hom.app (E.app M) (j ⁻¹ᵁ W) =
    Scheme.Modules.Hom.app (E.app M) (j ⁻¹ᵁ U.ι ⁻¹ᵁ A) ≫
      S.presheaf.map jt.op at hnE
  conv_rhs at hv => arg 2; arg 2; rw [← hnE]
  have hnJ := (Scheme.Modules.Hom.mapPresheaf (aj.unit.app R)).naturality t.op
  change R.presheaf.map t.op ≫ Scheme.Modules.Hom.app (aj.unit.app R) W =
    Scheme.Modules.Hom.app (aj.unit.app R) (U.ι ⁻¹ᵁ A) ≫
      (Lj.obj R).presheaf.map jt.op at hnJ
  conv_rhs at hv => arg 2; rw [← reassoc_of% hnJ]
  have hR := restrict_image_unit U.ι M W
  conv_rhs at hv => erw [reassoc_of% hR]
  let hW : U'.ι ''ᵁ (j ⁻¹ᵁ W) ≤ k ⁻¹ᵁ A := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨j y, hy, congrArg (fun q : U'.toScheme ⟶ X ↦ q y) hj⟩
  have hl := restriction_pushforward_transport k U.ι U'.ι j hj W T
  have hv' := (congrArg (fun q ↦ Scheme.Modules.Hom.app (ak.unit.app M) A ≫ q)
    hl.symm).trans hv
  have hr := congrArg (fun q ↦ Scheme.Modules.Hom.app q W) (aj.unit_naturality r)
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app] at hr
  rw [Scheme.Modules.Hom.comp_app]
  conv_lhs => rw [← Category.assoc]; arg 1; erw [hr]
  rw [Category.assoc]
  conv_lhs => arg 2; erw [← hv']


set_option maxRecDepth 2048 in
private theorem section_unit
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) (M : X.Modules) (W : U.toScheme.Opens) :
    let N := (schemeOpenRestriction X U).obj M
    let T := (Scheme.Modules.tensorPullback k).obj M
    let hW : U'.ι ''ᵁ (j ⁻¹ᵁ W) ≤ k ⁻¹ᵁ (U.ι ''ᵁ W) := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨j y, hy, congrArg (fun f : U'.toScheme ⟶ X ↦ f y) hj⟩
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app N).app W ≫
      Scheme.Modules.Hom.app
        ((openPinnedTensorRestrictionIso k U U' j hj).inv.app M ≫
          (Scheme.Modules.overFunctorEquiv U').hom.app T) (j ⁻¹ᵁ W) =
      ((Scheme.Modules.overFunctorEquiv U).hom.app M).app W ≫
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M).app
          (U.ι ''ᵁ W) ≫ T.presheaf.map (homOfLE hW).op := by
  dsimp only
  let ai := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)
  let ao := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U'.ι)
  let aj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)
  let ak := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  let ac := Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction (U'.ι ≫ k))
  let bi := Scheme.Modules.restrictAdjunction U.ι
  let bo := Scheme.Modules.restrictAdjunction U'.ι
  let ei := ai.leftAdjointUniq bi
  let eo := ao.leftAdjointUniq bo
  let cs := Scheme.Modules.tensorPullbackCompositionIso j U.ι (U'.ι ≫ k) hj
  let ct := Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl
  let qs := Scheme.Modules.pushforwardComp j U.ι ≪≫ Scheme.Modules.pushforwardCongr hj
  let qt := Scheme.Modules.pushforwardComp U'.ι k ≪≫ Scheme.Modules.pushforwardCongr rfl
  let E := Functor.isoWhiskerRight ei.symm (Scheme.Modules.tensorPullback j) ≪≫
    cs.symm ≪≫ ct ≪≫ Functor.isoWhiskerLeft (Scheme.Modules.tensorPullback k) eo
  have hei : conjugateEquiv ai bi ei.inv = 𝟙 _ := by
    change conjugateEquiv ai bi ((conjugateEquiv ai bi).symm (𝟙 _)) = _
    exact (conjugateEquiv ai bi).apply_symm_apply _
  have heo : conjugateEquiv bo ao eo.hom = 𝟙 _ := by
    change conjugateEquiv bo ao ((conjugateEquiv bo ao).symm (𝟙 _)) = _
    exact (conjugateEquiv bo ao).apply_symm_apply _
  have hcs : conjugateEquiv ac (ai.comp aj) cs.inv = qs.inv := by
    change conjugateEquiv ac (ai.comp aj)
      ((conjugateEquiv ac (ai.comp aj)).symm qs.inv) = _
    exact (conjugateEquiv ac (ai.comp aj)).apply_symm_apply _
  have hct : conjugateEquiv (ak.comp ao) ac ct.hom = qt.hom := by
    change conjugateEquiv (ak.comp ao) ac
      ((conjugateEquiv (ak.comp ao) ac).symm qt.hom) = _
    exact (conjugateEquiv (ak.comp ao) ac).apply_symm_apply _
  have hE : conjugateEquiv (ak.comp bo) (bi.comp aj) E.hom = qt.hom ≫ qs.inv := by
    dsimp only [E, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom]
    rw [← conjugateEquiv_comp (ak.comp bo) (ai.comp aj) (bi.comp aj),
      ← conjugateEquiv_comp (ak.comp bo) ac (ai.comp aj),
      ← conjugateEquiv_comp (ak.comp bo) (ak.comp ao) ac]
    rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, hei, heo, hcs, hct]
    rfl
  let r := (Scheme.Modules.overFunctorEquiv U).hom.app M
  let T := (Scheme.Modules.tensorPullback k).obj M
  have hOi : (openPinnedTensorOpenIso X U).inv.app M = r ≫ ei.inv.app M := by
    have h := congrArg (fun t ↦ t.app M) (open_normal X U)
    change (openPinnedTensorOpenIso X U).hom.app M ≫ r = ei.hom.app M at h
    rw [← cancel_epi ((openPinnedTensorOpenIso X U).hom.app M)]
    simp only [Iso.hom_inv_id_app, ← Category.assoc, h]
  have hF : (openPinnedTensorRestrictionIso k U U' j hj).inv.app M ≫
      (Scheme.Modules.overFunctorEquiv U').hom.app T =
      (Scheme.Modules.tensorPullback j).map r ≫ E.hom.app M := by
    simp only [openPinnedTensorRestrictionIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
    change (Scheme.Modules.tensorPullback j).map ((openPinnedTensorOpenIso X U).inv.app M) ≫
      cs.inv.app M ≫ ct.hom.app M ≫ (openPinnedTensorOpenIso X' U').hom.app T ≫
        (Scheme.Modules.overFunctorEquiv U').hom.app T = _
    rw [hOi, (Scheme.Modules.tensorPullback j).map_comp]
    have h := congrArg (fun t ↦ t.app T) (open_normal X' U')
    change (openPinnedTensorOpenIso X' U').hom.app T ≫
      (Scheme.Modules.overFunctorEquiv U').hom.app T = eo.hom.app T at h
    rw [h]
    rfl
  have hv := unit_sections_of_conjugate k U U' j hj
    (Scheme.Modules.tensorPullback k) (Scheme.Modules.tensorPullback j)
    ak aj E.hom hE M ((schemeOpenRestriction X U).obj M) r W
  exact (congrArg (fun q ↦
    Scheme.Modules.Hom.app (aj.unit.app ((schemeOpenRestriction X U).obj M)) W ≫
      Scheme.Modules.Hom.app q (j ⁻¹ᵁ W)) hF).trans hv

end

-- The germ argument uses arbitrary sheaves, so tensor constructions remain abstract.
private theorem stalk_unit_of_sections
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) (M : X.Modules) (N : U.toScheme.Modules)
    (T : X'.Modules) (P : U'.toScheme.Modules)
    (r : N ⟶ (Scheme.Modules.restrictFunctor U.ι).obj M)
    (a : N ⟶ (Scheme.Modules.pushforward j).obj P)
    (f : P ⟶ (Scheme.Modules.restrictFunctor U'.ι).obj T)
    (v : M ⟶ (Scheme.Modules.pushforward k).obj T)
    (hsections : ∀ (W : U.toScheme.Opens),
      let hW : U'.ι ''ᵁ (j ⁻¹ᵁ W) ≤ k ⁻¹ᵁ (U.ι ''ᵁ W) := by
        rintro x ⟨y, hy, rfl⟩
        exact ⟨j y, hy, congrArg (fun q : U'.toScheme ⟶ X ↦ q y) hj⟩
      Scheme.Modules.Hom.app a W ≫ Scheme.Modules.Hom.app f (j ⁻¹ᵁ W) =
        Scheme.Modules.Hom.app r W ≫ Scheme.Modules.Hom.app v (U.ι ''ᵁ W) ≫
          T.presheaf.map (homOfLE hW).op) (z : U'.toScheme) :
    let hx := congrArg (fun t : U'.toScheme ⟶ X ↦ t z) hj
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j z)).map
        (Scheme.Modules.Hom.mapPresheaf r) ≫
      (Scheme.Modules.restrictStalkNatIso U.ι (j z)).hom.app M ≫
      (M.presheaf.stalkCongr (.of_eq hx)).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k z.val)).map
        (Scheme.Modules.Hom.mapPresheaf v) ≫
      T.presheaf.stalkPushforward AddCommGrpCat.{u} k.base z.val =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j z)).map
        (Scheme.Modules.Hom.mapPresheaf a) ≫
      P.presheaf.stalkPushforward AddCommGrpCat.{u} j.base z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        (Scheme.Modules.Hom.mapPresheaf f) ≫
      (Scheme.Modules.restrictStalkNatIso U'.ι z).hom.app T := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  apply TopCat.Presheaf.stalk_hom_ext N.presheaf
  intro W hzW
  simp only [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkCongr_hom]
  rw [reassoc_of% (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι (j z) M hzW)]
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  have hzA : k z.val ∈ U.ι ''ᵁ W := by
    exact ⟨j z, hzW, congrArg (fun t : U'.toScheme ⟶ X ↦ t z) hj⟩
  erw [TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} k.base T.presheaf
    (U.ι ''ᵁ W) z.val hzA]
  erw [reassoc_of% (TopCat.Presheaf.stalkPushforward_germ
    AddCommGrpCat.{u} j.base P.presheaf W z hzW)]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  rw [Scheme.Modules.germ_restrictStalkNatIso_hom_app]
  have hzB : z.val ∈ U'.ι ''ᵁ (j ⁻¹ᵁ W) := ⟨z, hzW, rfl⟩
  have hs := congrArg (fun q ↦
    q ≫ T.presheaf.germ (U'.ι ''ᵁ (j ⁻¹ᵁ W)) z.val hzB)
    (hsections W)
  simp only [Category.assoc] at hs
  conv_rhs at hs => arg 2; arg 2; erw [TopCat.Presheaf.germ_res]
  exact hs.symm


set_option maxRecDepth 2048 in
/-- The pinned tensor restriction comparison preserves the pullback unit on stalks.

Proof: express the inverse comparison as the inverse of its four defining factors.
The open-pullback factor is the unique comparison of left adjoints; the identity
`Adjunction.unit_leftAdjointUniq_hom_app` says it identifies their units.
For each composition factor, `unit_conjugateEquiv_symm` identifies the composite
unit with the unit for the composite morphism, followed by the pushforward
composition comparison. The two composition comparisons cancel after transport
along `hj`. Hence the inverse pinned comparison sends the restricted unit for
`j` to the restriction of the unit for `k`. Apply the additive stalk functor,
then the pushforward-stalk map. On section germs this map sends the germ of a
unit section over W to its germ over the inverse image of W. The formulas
`germ_restrictStalkNatIso_hom_app` identify both open restriction factors with
the same ambient germ. Transport of the input point is exactly `hx` below.
Every stalk element is represented by a section germ, so equality on germs
proves the equality of additive maps. No flatness or cartesian hypothesis is
used. Empty opens have no z; zero sheaves and identity open immersions satisfy
the same unit identities.
Source: Stacks Project, Tags 0096 and 0098; Mathlib adjunction mate unit identities.
(blueprint: lem-pc-open-pinned-tensor-restriction-stalk-unit). -/
theorem openPinnedTensorRestriction_stalk_unit
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) (M : X.Modules) (z : U'.toScheme) :
    let N := (schemeOpenRestriction X U).obj M
    let L₀ := RingedSpace.moduleStalkFunctor U'.toScheme.toRingedSpace z
    let F₀ := forget₂ (ModuleCat.{u} (U'.toScheme.presheaf.stalk z)) AddCommGrpCat.{u}
    let Lᵢ := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace (j z)
    let Fᵢ := forget₂ (ModuleCat.{u} (U.toScheme.presheaf.stalk (j z))) AddCommGrpCat.{u}
    let γ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U') (L₀ ⋙ F₀) ≪≫
      Scheme.Modules.restrictStalkNatIso U'.ι z
    let γᵢ := Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) (Lᵢ ⋙ Fᵢ) ≪≫
      Scheme.Modules.restrictStalkNatIso U.ι (j z)
    let hx := congrArg (fun t : U'.toScheme ⟶ X ↦ t z) hj
    γᵢ.hom.app M ≫ (M.presheaf.stalkCongr (.of_eq hx)).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k z.val)).map
          (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)) ≫
        ((Scheme.Modules.tensorPullback k).obj M).presheaf.stalkPushforward
          AddCommGrpCat.{u} k.base z.val =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j z)).map
          (Scheme.Modules.Hom.mapPresheaf
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app N)) ≫
        ((Scheme.Modules.tensorPullback j).obj N).presheaf.stalkPushforward
          AddCommGrpCat.{u} j.base z ≫
        F₀.map (L₀.map ((openPinnedTensorRestrictionIso k U U' j hj).inv.app M)) ≫
        γ.hom.app ((Scheme.Modules.tensorPullback k).obj M) := by
  let N : U.toScheme.Modules := (schemeOpenRestriction X U).obj M
  let T := (Scheme.Modules.tensorPullback k).obj M
  let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)
  let r := (Scheme.Modules.overFunctorEquiv U).hom.app M
  let f := (openPinnedTensorRestrictionIso k U U' j hj).inv.app M ≫
    (Scheme.Modules.overFunctorEquiv U').hom.app T
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.comp_map, Category.assoc]
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j z)).map
      (Scheme.Modules.Hom.mapPresheaf r) ≫
      (Scheme.Modules.restrictStalkNatIso U.ι (j z)).hom.app M ≫ _ =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j z)).map
      (Scheme.Modules.Hom.mapPresheaf (a.unit.app N)) ≫
      ((Scheme.Modules.tensorPullback j).obj N).presheaf.stalkPushforward
        AddCommGrpCat.{u} j.base z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        (Scheme.Modules.Hom.mapPresheaf
          ((openPinnedTensorRestrictionIso k U U' j hj).inv.app M)) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        (Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.overFunctorEquiv U').hom.app T)) ≫
      (Scheme.Modules.restrictStalkNatIso U'.ι z).hom.app T
  rw [← CategoryTheory.Functor.map_comp_assoc
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z)]
  change _ = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j z)).map
      (Scheme.Modules.Hom.mapPresheaf (a.unit.app N)) ≫
      ((Scheme.Modules.tensorPullback j).obj N).presheaf.stalkPushforward
        AddCommGrpCat.{u} j.base z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        (Scheme.Modules.Hom.mapPresheaf f) ≫
      (Scheme.Modules.restrictStalkNatIso U'.ι z).hom.app T
  exact stalk_unit_of_sections k U U' j hj M N T _ r (a.unit.app N) f
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).unit.app M)
    (fun W ↦ section_unit k U U' j hj M W) z

end AlgebraicGeometry
