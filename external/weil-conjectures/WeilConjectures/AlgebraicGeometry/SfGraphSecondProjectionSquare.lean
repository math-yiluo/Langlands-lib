/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionStages
import all WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import all WeilConjectures.AlgebraicGeometry.SfGraphProjectionWord

/-! # Projection compatibility of the second graph side

Source: `LowerShriekComposition.lean`, eB, and Stacks Tags 0B56, 0GL1 and 0F7B.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] derivedTensor sfGraphWordProjection sfGraphSecondSideIso
  Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  upperStar lowerStar openImmersionLowerShriek rightDerivedLowerStarProjectionMap
  derivedOpenImmersionLowerShriekProjectionIso rightDerivedLowerStarComp
  leftDerivedUpperStarComp derivedSquareUpperStarIso openImmersionLowerShriekLowerStarExchange
  properStrength properTwistedStrength openStrength
attribute [local implicit_reducible] EtaleGraphPresentation.functor sfGraphSecondPresentation
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

private theorem paste_second
    {C D E P Q Z : Type*}
    [Category C] [Category D] [Category E] [Category P] [Category Q] [Category Z]
    (j : C ⥤ D) (q : D ⥤ E) (a : C ⥤ E) (i : E ⥤ Q) (b : D ⥤ P)
    (p : P ⥤ Q) (s : Q ⥤ Z) (r : P ⥤ Z)
    (TC : C ⥤ C) (TD : D ⥤ D) (TE : E ⥤ E)
    (TP : P ⥤ P) (TQ : Q ⥤ Q) (TZ : Z ⥤ Z)
    (tj : j ⋙ TD ⟶ TC ⋙ j) (tq : q ⋙ TE ⟶ TD ⋙ q)
    (ta : a ⋙ TE ⟶ TC ⋙ a) (ti : i ⋙ TQ ⟶ TE ⋙ i)
    (ts : s ⋙ TZ ⟶ TQ ⋙ s) (tb : b ⋙ TP ⟶ TD ⋙ b)
    (tp : p ⋙ TQ ⟶ TP ⋙ p) (tr : r ⋙ TZ ⟶ TP ⋙ r)
    (alpha : j ⋙ q ≅ a) (ex : q ⋙ i ⟶ b ⋙ p) (beta : p ⋙ s ⟶ r)
    (ha : ∀ M, TE.map (alpha.hom.app M) ≫ ta.app M =
      tq.app (j.obj M) ≫ q.map (tj.app M) ≫ alpha.hom.app (TC.obj M))
    (hm : ∀ M, ti.app (q.obj M) ≫ i.map (tq.app M) ≫ ex.app (TD.obj M) =
      TQ.map (ex.app M) ≫ tp.app (b.obj M) ≫ p.map (tb.app M))
    (hp : ∀ M, TZ.map (beta.app M) ≫ tr.app M =
      ts.app (p.obj M) ≫ s.map (tp.app M) ≫ beta.app (TP.obj M))
    (M : C) :
    let eta := fun N ↦ s.map (i.map (alpha.inv.app N)) ≫
      s.map (ex.app (j.obj N)) ≫ beta.app (b.obj (j.obj N))
    TZ.map (eta M) ≫ tr.app (b.obj (j.obj M)) ≫
        r.map (tb.app (j.obj M)) ≫ r.map (b.map (tj.app M)) =
      ts.app (i.obj (a.obj M)) ≫ s.map (ti.app (a.obj M)) ≫
        s.map (i.map (ta.app M)) ≫ eta (TC.obj M) := by
  intro eta
  apply (cancel_epi (TZ.map (s.map (i.map (alpha.hom.app M))))).1
  dsimp only [eta]
  simp only [Functor.map_comp, Category.assoc]
  rw [← TZ.map_comp_assoc, ← s.map_comp, ← i.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  have hs := ts.naturality (i.map (alpha.hom.app M))
  have hi := ti.naturality (alpha.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs hi
  rw [reassoc_of% hs]
  have hi' := congrArg s.map hi
  simp only [Functor.map_comp] at hi'
  rw [reassoc_of% hi']
  have ha' := congrArg (fun z ↦ s.map (i.map z)) (ha M)
  simp only [Functor.map_comp] at ha'
  rw [reassoc_of% ha']
  have hc : s.map (i.map (alpha.hom.app (TC.obj M))) ≫
      s.map (i.map (alpha.inv.app (TC.obj M))) = 𝟙 _ := by
    rw [← s.map_comp, ← i.map_comp, Iso.hom_inv_id_app]
    simp only [CategoryTheory.Functor.map_id]
  rw [reassoc_of% hc, reassoc_of% (hp (b.obj (j.obj M)))]
  have hn := ex.naturality (tj.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hn' := congrArg s.map hn
  have hm' := congrArg s.map (hm (j.obj M))
  simp only [Functor.map_comp] at hn' hm'
  have hs' := ts.naturality (ex.app (j.obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs'
  have hb := beta.naturality (tb.app (j.obj M) ≫ b.map (tj.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  simp only [Functor.map_comp, Category.assoc] at hb
  rw [reassoc_of% hs', ← hb]
  rw [← reassoc_of% hm', ← reassoc_of% hn']

private theorem paste_coefficients
    {C : Type*} [Category C]
    {W B₀ B₁ C₀ C₁ C₂ D₀ D₁ D₂ Z : C}
    (pi : W ⟶ B₀) (c : B₀ ⟶ B₁) (e' : B₁ ⟶ C₁) (w : C₁ ⟶ C₂)
    (a' : C₂ ⟶ D₂) (d : D₂ ⟶ Z) (e : B₀ ⟶ C₀) (u : C₀ ⟶ C₁)
    (a : C₀ ⟶ D₀) (v : D₀ ⟶ D₁) (w' : D₁ ⟶ D₂)
    (he : c ≫ e' = e ≫ u) (ha : u ≫ w ≫ a' = a ≫ v ≫ w') :
    (pi ≫ c) ≫ (e' ≫ w) ≫ (a' ≫ d) = pi ≫ e ≫ a ≫ v ≫ w' ≫ d := by
  simp only [Category.assoc]
  rw [reassoc_of% he, reassoc_of% ha]

section GenericWord

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
  {FC : B → B → Type*} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

private noncomputable def wordProjection
    {X U P Y : Scheme.{u}} (a : X ⟶ U) (e : U ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion e]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    {V : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (v : (upperStar B a).leftDerivedFunctor.obj
      ((upperStar B e).leftDerivedFunctor.obj
        ((upperStar B p).leftDerivedFunctor.obj K)) ⟶ V) :
    ((derivedTensor B Y).obj
      ((lowerStar B p).rightDerivedFunctor.obj
        ((openImmersionLowerShriek B e).mapDerivedCategory.obj
          ((lowerStar B a).rightDerivedFunctor.obj M)))).obj K ⟶
    (lowerStar B p).rightDerivedFunctor.obj
      ((openImmersionLowerShriek B e).mapDerivedCategory.obj
        ((lowerStar B a).rightDerivedFunctor.obj
          (((derivedTensor B X).obj M).obj V))) :=
  ((rightDerivedLowerStarProjectionMap B p).app
    ((openImmersionLowerShriek B e).mapDerivedCategory.obj
      ((lowerStar B a).rightDerivedFunctor.obj M))).app K ≫
  (lowerStar B p).rightDerivedFunctor.map
    (((derivedOpenImmersionLowerShriekProjectionIso B e).inv.app
      ((lowerStar B a).rightDerivedFunctor.obj M)).app
        ((upperStar B p).leftDerivedFunctor.obj K)) ≫
  (lowerStar B p).rightDerivedFunctor.map
    ((openImmersionLowerShriek B e).mapDerivedCategory.map
      (((rightDerivedLowerStarProjectionMap B a).app M).app
        ((upperStar B e).leftDerivedFunctor.obj
          ((upperStar B p).leftDerivedFunctor.obj K)))) ≫
  (lowerStar B p).rightDerivedFunctor.map
    ((openImmersionLowerShriek B e).mapDerivedCategory.map
      ((lowerStar B a).rightDerivedFunctor.map
        (((derivedTensor B X).obj M).map v)))

attribute [local irreducible] wordProjection

private theorem wordProjection_transport
    {X U P Y : Scheme.{u}} (a : X ⟶ U) (e : U ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion e]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (V : DerivedCategory (Sheaf P.smallEtaleTopology B))
    (W : DerivedCategory (Sheaf U.smallEtaleTopology B))
    {Z : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (v : (upperStar B p).leftDerivedFunctor.obj K ⟶ V)
    (w : (upperStar B e).leftDerivedFunctor.obj V ⟶ W)
    (d : (upperStar B a).leftDerivedFunctor.obj W ⟶ Z) :
    (properTwistedStrength B p K v).app
        ((openImmersionLowerShriek B e).mapDerivedCategory.obj
          ((lowerStar B a).rightDerivedFunctor.obj M)) ≫
      (lowerStar B p).rightDerivedFunctor.map
        ((openStrength B e V w).app ((lowerStar B a).rightDerivedFunctor.obj M)) ≫
      (lowerStar B p).rightDerivedFunctor.map
        ((openImmersionLowerShriek B e).mapDerivedCategory.map
          ((properTwistedStrength B a W d).app M)) =
    wordProjection B a e p M K
      ((upperStar B a).leftDerivedFunctor.map
        ((upperStar B e).leftDerivedFunctor.map v) ≫
        (upperStar B a).leftDerivedFunctor.map w ≫ d) := by
  have he := openProjection_naturality_right B e
    ((lowerStar B a).rightDerivedFunctor.obj M) _ _ v
  have he' := congrArg (lowerStar B p).rightDerivedFunctor.map he
  have ha := properProjection_naturality_right B a M _ _
    ((upperStar B e).leftDerivedFunctor.map v ≫ w)
  have ha' := congrArg
    ((openImmersionLowerShriek B e).mapDerivedCategory ⋙
      (lowerStar B p).rightDerivedFunctor).map ha
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at he' ha'
  have hh := paste_coefficients
    (((rightDerivedLowerStarProjectionMap B p).app
      ((openImmersionLowerShriek B e).mapDerivedCategory.obj
        ((lowerStar B a).rightDerivedFunctor.obj M))).app K)
    _ _ _ _
    ((lowerStar B p).rightDerivedFunctor.map
      ((openImmersionLowerShriek B e).mapDerivedCategory.map
        ((lowerStar B a).rightDerivedFunctor.map (((derivedTensor B X).obj M).map d))))
    _ _ _ _ _ he' ha'
  simpa only [properTwistedStrength_app, openStrength_app, wordProjection,
    Functor.comp_map, Functor.map_comp, Category.assoc] using hh

omit [UpperStarPreservesFlat B] in
private theorem second_coefficient
    {X O U T P Y : Scheme.{u}}
    (s : X ⟶ O) (q : O ⟶ U) (a : X ⟶ U) (b : O ⟶ T)
    (r : T ⟶ P) (e : U ⟶ P) (p : P ⟶ Y) (f : X ⟶ Y)
    (ha : a = s ≫ q) (sq : CommSq q b e r) (hf : f = (a ≫ e) ≫ p)
    (hn : f = (s ≫ b) ≫ (r ≫ p))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (upperStar B s).leftDerivedFunctor.map
        ((upperStar B b).leftDerivedFunctor.map
          ((leftDerivedUpperStarComp B r p).hom.app K)) ≫
      (upperStar B s).leftDerivedFunctor.map
        ((derivedSquareUpperStarIso B sq).hom.app
          ((upperStar B p).leftDerivedFunctor.obj K)) ≫
      (leftDerivedUpperStarComp B s q a ha).inv.app
        ((upperStar B e).leftDerivedFunctor.obj
          ((upperStar B p).leftDerivedFunctor.obj K)) ≫
      (leftDerivedUpperStarComp B a e).inv.app
        ((upperStar B p).leftDerivedFunctor.obj K) ≫
      (leftDerivedUpperStarComp B (a ≫ e) p f hf).inv.app K =
    (leftDerivedUpperStarComp B s b).inv.app
        ((upperStar B (r ≫ p)).leftDerivedFunctor.obj K) ≫
      (leftDerivedUpperStarComp B (s ≫ b) (r ≫ p) f hn).inv.app K := by
  have hab : a ≫ e = (s ≫ b) ≫ r := by
    rw [ha, Category.assoc, sq.w, ← Category.assoc]
  have h₁ := leftDerivedUpperStarComp_assoc'_app B (s ≫ b) r p
    (a ≫ e) (r ≫ p) f hab rfl hf K
  have h₂ := leftDerivedUpperStarComp_assoc'_app B s b r
    (s ≫ b) (q ≫ e) (a ≫ e) rfl sq.w hab
    ((upperStar B p).leftDerivedFunctor.obj K)
  have h₃ := leftDerivedUpperStarComp_assoc'_app B s q e
    a (q ≫ e) (a ≫ e) ha rfl rfl
    ((upperStar B p).leftDerivedFunctor.obj K)
  have hν := (leftDerivedUpperStarComp B s b).hom.naturality
    ((leftDerivedUpperStarComp B r p).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hν
  apply (cancel_epi ((leftDerivedUpperStarComp B (s ≫ b) (r ≫ p) f hn).hom.app K ≫
    (leftDerivedUpperStarComp B s b).hom.app
      ((upperStar B (r ≫ p)).leftDerivedFunctor.obj K))).1
  simp only [Category.assoc]
  rw [reassoc_of% hν.symm, reassoc_of% h₁, ← reassoc_of% h₂]
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h₃]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]

private theorem properStrength_compOfEq
    {X U P : Scheme.{u}} (s : X ⟶ U) (q : U ⟶ P) (a : X ⟶ P)
    (h : s ≫ q = a) (K : DerivedCategory (Sheaf P.smallEtaleTopology B))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((derivedTensor B P).flip.obj K).map
        ((rightDerivedLowerStarCompOfEq B s q a h).hom.app M) ≫
      (properTwistedStrength B a K
        ((leftDerivedUpperStarComp B s q a h.symm).hom.app K)).app M =
    (properStrength B q K).app ((lowerStar B s).rightDerivedFunctor.obj M) ≫
      (lowerStar B q).rightDerivedFunctor.map
        ((properStrength B s ((upperStar B q).leftDerivedFunctor.obj K)).app M) ≫
      (rightDerivedLowerStarCompOfEq B s q a h).hom.app
        (((derivedTensor B X).flip.obj
          ((upperStar B s).leftDerivedFunctor.obj
            ((upperStar B q).leftDerivedFunctor.obj K))).obj M) := by
  subst a
  exact properStrength_comp B s q K M

private noncomputable def secondSide
    {X O U T P Y : Scheme.{u}}
    (s : X ⟶ O) (q : O ⟶ U) (a : X ⟶ U) (b : O ⟶ T)
    (r : T ⟶ P) (e : U ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion e] [IsOpenImmersion b]
    (ha : s ≫ q = a) (sq : IsPullback q b e r) :
    (lowerStar B a).rightDerivedFunctor ⋙
      (openImmersionLowerShriek B e).mapDerivedCategory ⋙
      (lowerStar B p).rightDerivedFunctor ⟶
    (lowerStar B s).rightDerivedFunctor ⋙
      (openImmersionLowerShriek B b).mapDerivedCategory ⋙
      (lowerStar B (r ≫ p)).rightDerivedFunctor :=
  Functor.whiskerRight (rightDerivedLowerStarCompOfEq B s q a ha).inv _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (openImmersionLowerShriekLowerStarExchange B sq) _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (rightDerivedLowerStarComp B r p).hom)

attribute [local irreducible] secondSide

private theorem second_projection
    {X O U T P Y : Scheme.{u}}
    (s : X ⟶ O) (q : O ⟶ U) (a : X ⟶ U) (b : O ⟶ T)
    (r : T ⟶ P) (e : U ⟶ P) (p : P ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion e] [IsOpenImmersion b]
    (ha : s ≫ q = a) (sq : IsPullback q b e r) (hf : f = (a ≫ e) ≫ p)
    (hn : f = (s ≫ b) ≫ (r ≫ p))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((derivedTensor B Y).flip.obj K).map ((secondSide B s q a b r e p ha sq).app M) ≫
      wordProjection B s b (r ≫ p) M K
        ((leftDerivedUpperStarComp B s b).inv.app
            ((upperStar B (r ≫ p)).leftDerivedFunctor.obj K) ≫
          (leftDerivedUpperStarComp B (s ≫ b) (r ≫ p) f hn).inv.app K) =
    wordProjection B a e p M K
        ((leftDerivedUpperStarComp B a e).inv.app
            ((upperStar B p).leftDerivedFunctor.obj K) ≫
          (leftDerivedUpperStarComp B (a ≫ e) p f hf).inv.app K) ≫
      (secondSide B s q a b r e p ha sq).app
        (((derivedTensor B X).obj M).obj ((upperStar B f).leftDerivedFunctor.obj K)) := by
  let N := (upperStar B p).leftDerivedFunctor.obj K
  let P := (upperStar B e).leftDerivedFunctor.obj N
  let Q := (upperStar B r).leftDerivedFunctor.obj N
  let S := (upperStar B q).leftDerivedFunctor.obj P
  let Cq := leftDerivedUpperStarComp B s q a ha.symm
  let Cr := leftDerivedUpperStarComp B r p
  let delta := (derivedSquareUpperStarIso B sq.toCommSq).hom.app N
  let alpha := rightDerivedLowerStarCompOfEq B s q a ha
  let gamma := openImmersionLowerShriekLowerStarExchange B sq
  let beta := (rightDerivedLowerStarComp B r p).hom
  let cold := (leftDerivedUpperStarComp B a e).inv.app N ≫
    (leftDerivedUpperStarComp B (a ≫ e) p f
      hf).inv.app K
  let cnew := (leftDerivedUpperStarComp B s b).inv.app
      ((upperStar B (r ≫ p)).leftDerivedFunctor.obj K) ≫
    (leftDerivedUpperStarComp B (s ≫ b) (r ≫ p) f hn).inv.app K
  let d := Cq.inv.app P ≫ cold
  have hc : (upperStar B s).leftDerivedFunctor.map
        ((upperStar B b).leftDerivedFunctor.map (Cr.hom.app K)) ≫
      (upperStar B s).leftDerivedFunctor.map delta ≫ d = cnew :=
    second_coefficient B s q a b r e p f ha.symm sq.toCommSq hf hn K
  let Rs := (lowerStar B s).rightDerivedFunctor
  let Rq := (lowerStar B q).rightDerivedFunctor
  let Ra := (lowerStar B a).rightDerivedFunctor
  let Je := (openImmersionLowerShriek B e).mapDerivedCategory
  let Jb := (openImmersionLowerShriek B b).mapDerivedCategory
  let Rr := (lowerStar B r).rightDerivedFunctor
  let Rp := (lowerStar B p).rightDerivedFunctor
  let Rrp := (lowerStar B (r ≫ p)).rightDerivedFunctor
  let TC := (derivedTensor B X).flip.obj ((upperStar B s).leftDerivedFunctor.obj S)
  let nproj : ((derivedTensor B Y).flip.obj K).obj (Rrp.obj (Jb.obj (Rs.obj M))) ⟶
      Rrp.obj (Jb.obj (Rs.obj (TC.obj M))) :=
    (properTwistedStrength B (r ≫ p) K (Cr.hom.app K)).app
      (Jb.obj (Rs.obj M)) ≫
    Rrp.map ((openStrength B b Q delta).app (Rs.obj M)) ≫
    Rrp.map (Jb.map ((properStrength B s S).app M))
  let oproj : ((derivedTensor B Y).flip.obj K).obj (Rp.obj (Je.obj (Ra.obj M))) ⟶
      Rp.obj (Je.obj (Ra.obj (TC.obj M))) :=
    (properStrength B p K).app (Je.obj (Ra.obj M)) ≫
    Rp.map ((openStrength B e N (𝟙 P)).app (Ra.obj M)) ≫
    Rp.map (Je.map ((properTwistedStrength B a P (Cq.hom.app P)).app M))
  have raw := paste_second Rs Rq Ra Je Jb Rr Rp Rrp
    TC ((derivedTensor B _).flip.obj S) ((derivedTensor B _).flip.obj P)
    ((derivedTensor B _).flip.obj Q) ((derivedTensor B _).flip.obj N)
    ((derivedTensor B Y).flip.obj K)
    (properStrength B s S) (properStrength B q P)
    (properTwistedStrength B a P (Cq.hom.app P))
    (openStrength B e N (𝟙 P)) (properStrength B p K)
    (openStrength B b Q delta) (properStrength B r N)
    (properTwistedStrength B (r ≫ p) K (Cr.hom.app K))
    alpha gamma beta
    (properStrength_compOfEq B s q a ha P)
    (fun V ↦ by
      have h := mixed_twisted_projection B sq N P (𝟙 P) V
      have hid : (derivedSquareUpperStarIso B sq.toCommSq).hom.app N ≫
          (upperStar B q).leftDerivedFunctor.map (𝟙 P) =
          (derivedSquareUpperStarIso B sq.toCommSq).hom.app N := by
        rw [(upperStar B q).leftDerivedFunctor.map_id P]
        exact Category.comp_id _
      rw [hid] at h
      exact h)
    (properStrength_comp B r p K) M
  have he (V : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
      Rp.map (Je.map (alpha.inv.app V)) ≫ Rp.map (gamma.app (Rs.obj V)) ≫
        beta.app (Jb.obj (Rs.obj V)) =
      (secondSide B s q a b r e p ha sq).app V := by
    simp only [secondSide, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Functor.comp_map]
    rfl
  dsimp only at raw
  rw [he M, he (TC.obj M)] at raw
  have hraw : ((derivedTensor B Y).flip.obj K).map
        ((secondSide B s q a b r e p ha sq).app M) ≫ nproj =
      oproj ≫ (secondSide B s q a b r e p ha sq).app (TC.obj M) := by
    simpa only [nproj, oproj, Category.assoc] using raw
  have hnew : nproj ≫ Rrp.map (Jb.map (Rs.map (((derivedTensor B X).obj M).map d))) =
      wordProjection B s b (r ≫ p) M K cnew := by
    have h := wordProjection_transport B s b (r ≫ p) M K Q S
      (Cr.hom.app K) delta d
    have hh := h.trans (congrArg (fun z ↦ wordProjection B s b (r ≫ p) M K z) hc)
    simpa only [nproj, properTwistedStrength_app, properStrength_app,
      Functor.map_comp, Category.assoc] using hh
  have hold : oproj ≫ Rp.map (Je.map (Ra.map (((derivedTensor B X).obj M).map d))) =
      wordProjection B a e p M K cold := by
    have hd : Cq.hom.app P ≫ d = cold := by
      simp only [d, Iso.hom_inv_id_app_assoc]
    rw [← hd]
    simp only [oproj, wordProjection, properTwistedStrength_app, properStrength_app,
      openStrength_app, Functor.map_comp, Category.assoc]
    rw [((derivedTensor B U).obj (Ra.obj M)).map_id P,
      (openImmersionLowerShriek B e).mapDerivedCategory.map_id
        (((derivedTensor B U).obj (Ra.obj M)).obj P),
      Rp.map_id ((openImmersionLowerShriek B e).mapDerivedCategory.obj
        (((derivedTensor B U).obj (Ra.obj M)).obj P))]
    exact congrArg
      (fun z ↦ ((rightDerivedLowerStarProjectionMap B p).app (Je.obj (Ra.obj M))).app K ≫
        Rp.map (((derivedOpenImmersionLowerShriekProjectionIso B e).inv.app
          (Ra.obj M)).app N) ≫ z)
      (Category.id_comp
        (Rp.map (Je.map (((rightDerivedLowerStarProjectionMap B a).app M).app P)) ≫
          Rp.map (Je.map (Ra.map (((derivedTensor B X).obj M).map (Cq.hom.app P)))) ≫
          Rp.map (Je.map (Ra.map (((derivedTensor B X).obj M).map d)))))
  have hnat := (secondSide B s q a b r e p ha sq).naturality
    (((derivedTensor B X).obj M).map d)
  change Rp.map (Je.map (Ra.map (((derivedTensor B X).obj M).map d))) ≫
      (secondSide B s q a b r e p ha sq).app
        (((derivedTensor B X).obj M).obj ((upperStar B f).leftDerivedFunctor.obj K)) =
    (secondSide B s q a b r e p ha sq).app (TC.obj M) ≫
      Rrp.map (Jb.map (Rs.map (((derivedTensor B X).obj M).map d))) at hnat
  have result := congrArg
    (fun z ↦ z ≫ Rrp.map (Jb.map (Rs.map (((derivedTensor B X).obj M).map d)))) hraw
  simp only [Category.assoc] at result
  rw [hnew, ← hnat, ← Category.assoc, hold] at result
  exact result

end GenericWord

private theorem wordProjection_graph
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    sfGraphWordProjection A t M K =
      wordProjection (ModuleCat.{u + 1} A) t.a t.e t.p M K
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) t.a t.e).inv.app
            ((upperStar (ModuleCat.{u + 1} A) t.p).leftDerivedFunctor.obj K) ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (t.a ≫ t.e) t.p f
            ((Category.assoc t.a t.e t.p).trans t.fac).symm).inv.app K) := by
  simp only [sfGraphWordProjection, sfGraphProjectionWord, wordProjection, Functor.map_comp]

/-- Projection compatibility of the second graph side.

Source: `LowerShriekComposition.lean`, eB; the tensor calculation uses Stacks
Tags 0B56, 0GL1 and 0F7B (auxiliary; not a blueprint node).

Proof in words. Expand B2 into the inverse direct-image compositor for s2 q2 = a, the
Cartesian proper/open exchange over e, and the direct-image compositor for p1 p.
The proper projection composition identity, solved for the inverse compositor,
splits the projection for a into the successive projections for q2 and s2.
Whisker the proper/open tensor square for O2 = (P x_Y C) x_P U by Rs2 on its
source side and Rp on its target side. Compose the outer proper projections
using the normalized direct-image composition identity. Naturality allows the
projection for s2 to pass the exchange. Pullback-composition coherence equates
the two resulting coefficient paths: both are the canonical comparison from
Lp Le La to Lf through s2 b2 p1 p = f. Thus all three constituent squares paste
to the stated equation. The compositor components, rather than any projection,
are inverted; arbitrary unbounded inputs and arbitrary supporting opens suffice.
-/
theorem sfGraphSecondSideIso_projection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (t : EtaleGraphPresentation f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((sfGraphSecondSideIso c t A).hom.app M)).app K ≫
      sfGraphWordProjection A (sfGraphSecondPresentation c t) M K =
    sfGraphWordProjection A (t) M K ≫
      (sfGraphSecondSideIso c t A).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) := by
  let s := locallyClosedGraphS₂ t.a t.e t.p c.i c.g
    ((Category.assoc _ _ _).trans (t.fac.trans c.comm))
  let q := pullback.snd (pullback.fst t.p c.g) t.e
  let b := pullback.fst (pullback.fst t.p c.g) t.e
  let r := pullback.fst t.p c.g
  have ha : s ≫ q = t.a := by simp only [s, q, locallyClosedGraphS₂, pullback.lift_snd]
  let sq := (IsPullback.of_hasPullback r t.e).flip
  have hn : f = (s ≫ b) ≫ (r ≫ t.p) := by
    simpa only [sfGraphSecondPresentation, s, b, r, Category.assoc] using
      (sfGraphSecondPresentation c t).fac.symm
  have h := second_projection (ModuleCat.{u + 1} A) s q t.a b r t.e t.p f ha sq
    ((Category.assoc _ _ _).trans t.fac).symm hn M K
  have he (V : DerivedCategoryModule A X) :
      (secondSide (ModuleCat.{u + 1} A) s q t.a b r t.e t.p ha sq).app V =
      (sfGraphSecondSideIso c t A).hom.app V := by
    simp only [secondSide, sfGraphSecondSideIso, locallyClosedGraphSide₂,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Functor.comp_map, rightDerivedLowerStarCompOfEq, openImmersionLowerShriekLowerStarExchangeIso,
      asIso_hom]
    rfl
  rw [he M, he _] at h
  rw [wordProjection_graph A t M K, wordProjection_graph A (sfGraphSecondPresentation c t) M K]
  exact h

end AlgebraicGeometry.Etale
