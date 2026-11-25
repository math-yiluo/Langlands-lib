/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLimitSheafApproximation.AffineLimitSheafApproximation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic

import WeilConjectures.AlgebraicGeometry.Sites.GmGenericPoint
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteDiagramDescent
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Eventual vanishing in the kernel of an approximation counit

Source: blueprint `lemma-uniform-bounds-pro-etale-affines`, proof step 1, injectivity argument.
(blueprint: lem-sc-affine-limit-sheaf-approximation-germ-kernel). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme

private theorem lowerStarComp_inv_sections
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ Z) (r : X ⟶ Z) (hr : r = p ≫ f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : Z.Etale) :
    ((Etale.lowerStarComp AddCommGrpCat.{u + 1} p f r hr).inv.app F).hom.app (op V) =
      F.obj.map ((MorphismProperty.Over.pullbackComp p f r hr).inv.app V).op := by
  let δ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) p f r hr
  let c := Etale.lowerStarComp AddCommGrpCat.{u + 1} p f r hr
  apply (cancel_mono (F.obj.map (δ.hom.app V).op)).mp
  calc
    _ = ((c.inv.app F ≫ c.hom.app F).hom.app (op V)) := by
      rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
      rw [Etale.lowerStarComp_hom_app_hom_app]
    _ = 𝟙 _ := by rw [Iso.inv_hom_id_app]; rfl
    _ = _ := by
      simp [δ, ← F.obj.map_comp, ← op_comp]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem approximationMap_unit_sections
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (f : Y ⟶ Z) (r : X ⟶ Z) (hr : r = p ≫ f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Z.Etale) (W : Y.Etale) (h : W ⟶ f.Etale.obj V) :
    let Q := (Etale.upperStar AddCommGrpCat.{u + 1} p).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F)
    let δ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) p f r hr
    let g := p.Etale.map h ≫ δ.inv.app V
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} r).unit.app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} r).obj F)).hom.app (op V) ≫
        (Etale.AffineLimitSheafApproximation.approximationMap p f r hr F).hom.app
          (op (r.Etale.obj V)) ≫ Q.obj.map g.op =
      F.obj.map g.op ≫
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app
          ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F)).hom.app (op W) := by
  dsimp only
  have ht := congrArg (fun k ↦ k.hom.app (op V))
    (Etale.AffineLimitSheafApproximation.approximationMap_transpose p f r hr F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at ht
  erw [← Category.assoc, ht]
  rw [Etale.lowerStarComp_hom_app_hom_app, lowerStarComp_inv_sections]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp, ← op_comp]
  rw [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact congrArg (fun k ↦ F.obj.map
    ((MorphismProperty.Over.pullbackComp p f r hr).inv.app V).op ≫ k)
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F)).hom.naturality h.op).symm

private theorem exists_qcqs_model_over
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s) (i : I) (W : s.pt.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    ∃ (j : I) (_ : j ⟶ i) (Wj : (D.obj j).Etale)
      (_ : (MorphismProperty.Over.pullback @Etale ⊤ (s.π.app j)).obj Wj ≅ W),
      CompactSpace Wj.left ∧ QuasiSeparatedSpace Wj.left := by
  classical
  obtain ⟨J, hJ, hd, hn, G, hG⟩ := IsFiltered.exists_directed (Over i)ᵒᵖ
  let := hJ
  let := hd
  let := hn
  let := hG
  let H := G.leftOp ⋙ Over.forget i
  let E := H ⋙ D
  have (j : Jᵒᵖ) : CompactSpace (E.obj j) :=
    inferInstanceAs (CompactSpace (D.obj (H.obj j)))
  have (j : Jᵒᵖ) : QuasiSeparatedSpace (E.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (H.obj j)))
  have {j k : Jᵒᵖ} (f : j ⟶ k) : IsAffineHom (E.map f) :=
    inferInstanceAs (IsAffineHom (D.map (H.map f)))
  let t := s.whisker H
  have ht : IsLimit t := (Functor.Initial.isLimitWhiskerEquiv H s).symm hs
  obtain ⟨j, Wj, _, _, e, _, hc, _, _⟩ :=
    Etale.exists_etale_limit_finite_diagram_descent E t ht W PEmpty
      (fun k ↦ PEmpty.elim k) (fun k ↦ PEmpty.elim k) (fun k ↦ PEmpty.elim k)
  exact ⟨(G.obj j).unop.left, (G.obj j).unop.hom, Wj, e, hc⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_qcqs_model_map
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s) (i : I) (V : (D.obj i).Etale)
    (W : s.pt.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (g : W ⟶ (s.π.app i).Etale.obj V) :
    ∃ (j : I) (f : j ⟶ i) (Wj : (D.obj j).Etale)
      (e : (s.π.app j).Etale.obj Wj ≅ W) (r : Wj.left ⟶ V.left),
      CompactSpace Wj.left ∧ QuasiSeparatedSpace Wj.left ∧
      r ≫ V.hom = Wj.hom ≫ D.map f ∧
      e.hom.left ≫ g.left ≫ pullback.fst V.hom (s.π.app i) =
        pullback.fst Wj.hom (s.π.app j) ≫ r := by
  classical
  obtain ⟨j, f, Wj, e, hc, hqs⟩ := exists_qcqs_model_over D s hs i W
  have : CompactSpace Wj.left := hc
  have : QuasiSeparatedSpace Wj.left := hqs
  have : CompactSpace ((𝟭 Scheme).obj Wj.left) := hc
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj Wj.left) := hqs
  let B := baseChangeDiagram D Wj.hom
  have (k : Over j) : CompactSpace (B.obj k) :=
    inferInstanceAs (CompactSpace ((baseChangeDiagram D Wj.hom).obj k))
  have (k : Over j) : QuasiSeparatedSpace (B.obj k) :=
    inferInstanceAs (QuasiSeparatedSpace ((baseChangeDiagram D Wj.hom).obj k))
  have {k l : Over j} (a : k ⟶ l) : IsAffineHom (B.map a) :=
    inferInstanceAs (IsAffineHom ((baseChangeDiagram D Wj.hom).map a))
  let b := baseChangeCone D s Wj.hom
  let τ := baseChangeDiagramStructure D Wj.hom ≫ (Functor.const (Over j)).map (D.map f)
  let a := e.hom.left ≫ g.left ≫ pullback.fst V.hom (s.π.app i)
  have ha : b.π ≫ τ = (Functor.const (Over j)).map (a ≫ V.hom) := by
    apply NatTrans.ext
    funext k
    change (baseChangeCone D s Wj.hom).π.app k ≫
      (pullback.fst Wj.hom (D.map k.hom) ≫ Wj.hom) ≫ D.map f =
        (e.hom.left ≫ g.left ≫ pullback.fst V.hom (s.π.app i)) ≫ V.hom
    simp only [← Category.assoc]
    rw [baseChangeCone_π_app_fst]
    calc
      _ = pullback.snd Wj.hom (s.π.app j) ≫ s.π.app i := by
        rw [pullback.condition, Category.assoc, s.w f]
      _ = _ := by
        simp only [Category.assoc]
        erw [pullback.condition]
        have hg : g.left ≫ pullback.snd V.hom (s.π.app i) = W.hom :=
          MorphismProperty.Over.w g
        have he : e.hom.left ≫ W.hom = pullback.snd Wj.hom (s.π.app j) :=
          MorphismProperty.Over.w e.hom
        rw [← Category.assoc g.left, hg, ← Category.assoc, he]
  obtain ⟨k, r, hkr, hr⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    B τ V.hom b (isLimitBaseChangeCone D s Wj.hom hs) a ha
  let Wk := (D.map k.hom).Etale.obj Wj
  let δ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (s.π.app k.left) (D.map k.hom) (s.π.app j) (s.w k.hom).symm
  let ek : (s.π.app k.left).Etale.obj Wk ≅ W := (δ.app Wj).symm ≪≫ e
  have hM : (δ.inv.app Wj).left ≫ b.π.app k =
      pullback.fst Wk.hom (s.π.app k.left) := by
    apply pullback.hom_ext
    · simp [δ, b, baseChangeCone, Wk]
      rfl
    · simp only [Functor.const_obj_obj, Functor.comp_obj,
        MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.pullback_obj_hom,
        Functor.id_obj, baseChangeDiagram_obj, MorphismProperty.Over.pullbackComp_inv_app_left,
        baseChangeCone, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd_assoc, δ, Wk, b]
      change pullback.snd (pullback.snd Wj.hom (D.map k.hom)) (s.π.app k.left) ≫
        s.π.app k.left = pullback.fst (pullback.snd Wj.hom (D.map k.hom))
          (s.π.app k.left) ≫ pullback.snd Wj.hom (D.map k.hom)
      exact pullback.condition.symm
  refine ⟨k.left, k.hom ≫ f, Wk, ek, r, ?_, ?_, ?_, ?_⟩
  · exact QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst Wj.hom (D.map k.hom))
  · exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst Wj.hom (D.map k.hom))
  · calc
      r ≫ V.hom = (pullback.fst Wj.hom (D.map k.hom) ≫ Wj.hom) ≫ D.map f := hr
      _ = Wk.hom ≫ D.map (k.hom ≫ f) := by
        change _ = pullback.snd Wj.hom (D.map k.hom) ≫ D.map (k.hom ≫ f)
        rw [D.map_comp, ← Category.assoc, pullback.condition, Category.assoc]
  · change (δ.inv.app Wj).left ≫ a = _
    rw [← hkr, ← Category.assoc, hM]

private theorem exists_kernel_germ_representative
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (t : ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F)))
    (ht : ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).counit.app F) t = 0) :
    ∃ (V : Y.Etale) (v : (pointSmallEtale (x ≫ p)).fiber.obj V)
      (a : F.obj.obj (op (p.Etale.obj V))) (W : X.Etale)
      (g : W ⟶ p.Etale.obj V) (w : (pointSmallEtale x).fiber.obj W),
      IsAffine W.left ∧
      (pointSmallEtale x).fiber.map g w =
        (pointSmallEtaleFiberEtaleIso p x).inv.app V v ∧
      F.obj.map g.op a = 0 ∧
      ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} p x).inv.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F))
        ((pointSmallEtale (x ≫ p)).toPresheafFiber V v
          ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F).obj a) = t := by
  classical
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let R := (Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F
  let e := (Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} p x).app R
  obtain ⟨V, v, a, ha⟩ :=
    (pointSmallEtale (x ≫ p)).toPresheafFiber_jointly_surjective (P := R.obj) (e.hom t)
  have he : e.inv ((pointSmallEtale (x ≫ p)).toPresheafFiber V v R.obj a) = t := by
    rw [ha]
    exact ConcreteCategory.congr_hom e.hom_inv_id t
  have hh := ConcreteCategory.congr_hom
    (Etale.upperStarCompSheafFiberIso_inv_app_comp_sheafFiber_map p x (𝟙 R))
      ((pointSmallEtale (x ≫ p)).toPresheafFiber V v R.obj a)
  have hid : ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).homEquiv
      R F).symm (𝟙 R) =
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).counit.app F :=
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).homEquiv_symm_id F
  rw [hid] at hh
  simp only [ConcreteCategory.comp_apply] at hh
  have hz : Etale.stalkComparison p x (𝟙 R)
      ((pointSmallEtale (x ≫ p)).toPresheafFiber V v R.obj a) = 0 := by
    rw [← hh]
    change ((pointSmallEtale x).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).counit.app F)
        (e.inv ((pointSmallEtale (x ≫ p)).toPresheafFiber V v R.obj a)) = 0
    rw [he]
    exact ht
  have h₁ := ConcreteCategory.congr_hom
    (Etale.toPresheafFiber_stalkComparison p x (𝟙 R) V v) a
  simp only [ConcreteCategory.comp_apply] at h₁
  obtain ⟨W, g, w, hw, hgw⟩ := ((pointSmallEtale x).toPresheafFiber_eq_iff' _ _ _ _).1
    (h₁.symm.trans (hz.trans (map_zero _).symm))
  change F.obj.map g.op a = F.obj.map g.op 0 at hgw
  have hzero : F.obj.map g.op a = 0 := by simpa only [map_zero] using hgw
  obtain ⟨W', ⟨k⟩⟩ := AffinePointedEtaleNeighborhood.exists_hom x ⟨w⟩
  refine ⟨V, v, a, W'.obj.1, k.1 ≫ g, W'.obj.2, W'.property, ?_, ?_, he⟩
  · have hk : (pointSmallEtale x).fiber.map k.1 W'.obj.2 = w := k.2
    simp only [Functor.map_comp, ConcreteCategory.comp_apply]
    exact (congrArg (fun z ↦ (pointSmallEtale x).fiber.map g z) hk).trans hw
  · rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, hzero, map_zero]

private theorem inverse_stalk_iso_germ_unit
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (V : Y.Etale) (v : (pointSmallEtale (x ≫ p)).fiber.obj V)
    (a : F.obj.obj (op (p.Etale.obj V))) :
    ((Etale.upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} p x).inv.app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F))
      ((pointSmallEtale (x ≫ p)).toPresheafFiber V v
        ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F).obj a) =
    (pointSmallEtale x).toPresheafFiber (p.Etale.obj V)
      ((pointSmallEtaleFiberEtaleIso p x).inv.app V v)
      ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F)).obj
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F)).hom.app (op V) a) := by
  let R := (Etale.lowerStar AddCommGrpCat.{u + 1} p).obj F
  let η := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).unit.app R
  have hh := Etale.upperStarCompSheafFiberIso_inv_app_comp_sheafFiber_map p x η
  have hid : ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).homEquiv
      R ((Etale.upperStar AddCommGrpCat.{u + 1} p).obj R)).symm η = 𝟙 _ :=
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} p).homEquiv_symm_unit R
  erw [hid] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  have h₁ := ConcreteCategory.congr_hom
    (Etale.toPresheafFiber_stalkComparison p x η V v) a
  simp only [ConcreteCategory.comp_apply] at h₁
  rw [← hh] at h₁
  exact h₁

/-- A germ killed by an approximation counit dies at a later stage.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-sc-cd-affine-limit.md,
proof step 1, the injectivity argument by finite-data descent.
(blueprint: lem-sc-affine-limit-sheaf-approximation-germ-kernel).

Proof: Identify the stalk of pᵢ⁻¹pᵢ*F at x with the stalk of pᵢ*F at pᵢ(x).
Represent the latter germ by a section a of F on the limit pullback of an
étale neighbourhood Vᵢ. The counit sends it to the germ of that section on
the limit. Its vanishing gives an étale neighbourhood W of the lifted point
and a map W → Vᵢ × X on which a restricts to zero. Refine W around the point
by an affine étale neighbourhood. Use a final directed reindexing and finite
étale-data descent to descend W. Over that model, the limit is a base-changed
limit. Since Vᵢ is étale, hence locally of finite presentation over Xᵢ,
Mathlib's factorization theorem descends the map to Vᵢ to a common stage j over i.
The point of W projects to a point of this stage model. The zero section
on W is literally a section of pⱼ*F on that model. The inverse-image unit
therefore makes its germ zero in pⱼ⁻¹pⱼ*F. Naturality of the units and the
composition isomorphisms identifies this germ with the transition image of
the original germ. Return along the reindexing functor to obtain j → i in
the original cofiltered category. Only one local representative and its
zero relation are descended; no cohomological bound is assumed. Empty
neighbourhoods have no pointed germs, and a zero germ may use the identity
transition, so no nonzero or nonempty-section hypothesis is needed. -/
theorem affineLimitSheafApproximation_germ_eventually_zero
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s)
    (F : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) (x : s.pt) :
    let A := Etale.AffineLimitSheafApproximation.approximationDiagram D s F
    let P : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
      (pointSmallEtale (s.pt.algClosurePoint x)).sheafFiber
    ∀ (i : Iᵒᵖ) (t : P.obj (A.obj i)),
      P.map ((Etale.AffineLimitSheafApproximation.approximationCocone D s F).ι.app i) t = 0 →
        ∃ (j : Iᵒᵖ) (f : i ⟶ j), P.map (A.map f) t = 0 := by
  classical
  dsimp only
  intro i t ht
  let z := s.pt.algClosurePoint x
  obtain ⟨V, v, a, W, g, w, hW, hgw, hzero, he⟩ :=
    exists_kernel_germ_representative (s.π.app i.unop) F z t ht
  have : IsAffine W.left := hW
  obtain ⟨j, f, Wj, e, r, hc, hqs, hr, hrg⟩ :=
    exists_qcqs_model_map D s hs i.unop V W g
  let h : Wj ⟶ (D.map f).Etale.obj V :=
    MorphismProperty.Over.homMk (pullback.lift r Wj.hom hr)
      (by exact pullback.lift_snd r Wj.hom hr)
  let δ := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    (s.π.app j) (D.map f) (s.π.app i.unop) (s.w f).symm
  let g' := (s.π.app j).Etale.map h ≫ δ.inv.app V
  have hgg : g' = e.hom ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change ((s.π.app j).Etale.map h).left ≫
        (δ.inv.app V).left ≫ pullback.fst V.hom (s.π.app i.unop) = _
      simp only [Functor.const_obj_obj, Functor.id_obj,
        MorphismProperty.Over.pullback_obj_left, Functor.comp_obj,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback_obj_hom,
        NatIso.ofComponents_inv_app, MorphismProperty.Over.isoMk_inv_left,
        Iso.trans_inv, Iso.symm_inv, pullback.congrHom_inv, Category.assoc,
        limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst, h, δ]
      erw [MorphismProperty.Over.pullback_map_left]
      erw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst]
      exact hrg.symm
    · exact (MorphismProperty.Over.w g').trans
        (MorphismProperty.Over.w (e.hom ≫ g)).symm
  have hzero' : F.obj.map g'.op a = 0 := by
    rw [hgg, op_comp, F.obj.map_comp, ConcreteCategory.comp_apply]
    exact (congrArg (fun b ↦ F.obj.map e.hom.op b) hzero).trans (map_zero _)
  refine ⟨op j, f.op, ?_⟩
  let P := pointSmallEtale z
  let wj := P.fiber.map e.inv w
  let vi := (pointSmallEtaleFiberEtaleIso (s.π.app i.unop) z).inv.app V v
  let Qi := (Etale.upperStar AddCommGrpCat.{u + 1} (s.π.app i.unop)).obj
    ((Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app i.unop)).obj F)
  let Qj := (Etale.upperStar AddCommGrpCat.{u + 1} (s.π.app j)).obj
    ((Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app j)).obj F)
  let ηi := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (s.π.app i.unop)).unit.app
      ((Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app i.unop)).obj F)
  let T := Etale.AffineLimitSheafApproximation.approximationMap
    (s.π.app j) (D.map f) (s.π.app i.unop) (s.w f).symm F
  have hpoint : P.fiber.map g' wj = vi := by
    dsimp only [wj]
    rw [← ConcreteCategory.comp_apply, ← P.fiber.map_comp, hgg]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact hgw
  have hrep : t = P.toPresheafFiber ((s.π.app i.unop).Etale.obj V) vi Qi.obj
      (ηi.hom.app (op V) a) :=
    he.symm.trans (inverse_stalk_iso_germ_unit (s.π.app i.unop) F z V v a)
  have hu := ConcreteCategory.congr_hom
    (approximationMap_unit_sections (s.π.app j) (D.map f)
      (s.π.app i.unop) (s.w f).symm F V Wj h) a
  simp only [ConcreteCategory.comp_apply] at hu
  have hz : Qj.obj.map g'.op (T.hom.app (op ((s.π.app i.unop).Etale.obj V))
      (ηi.hom.app (op V) a)) = 0 := by
    exact hu.trans ((congrArg (fun b ↦
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (s.π.app j)).unit.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app j)).obj F)).hom.app (op Wj) b)
      hzero').trans (map_zero _))
  have hn := ConcreteCategory.congr_hom
    (P.toPresheafFiber_naturality T.hom ((s.π.app i.unop).Etale.obj V) vi)
      (ηi.hom.app (op V) a)
  simp only [ConcreteCategory.comp_apply] at hn
  have hw := ConcreteCategory.congr_hom
    (P.toPresheafFiber_w g' wj Qj.obj)
      (T.hom.app (op ((s.π.app i.unop).Etale.obj V)) (ηi.hom.app (op V) a))
  simp only [ConcreteCategory.comp_apply] at hw
  rw [hpoint] at hw
  change P.sheafFiber.map T t = 0
  rw [hrep]
  exact hn.trans (hw.symm.trans (by rw [hz, map_zero]))

end AlgebraicGeometry.Scheme
