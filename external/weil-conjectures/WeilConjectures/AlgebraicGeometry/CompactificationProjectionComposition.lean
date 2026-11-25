/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.OpenImmersionProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat

/-! # Projection maps on a compatible compactification tower

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B and 0F7J,
and Cohomology on Sites, Tag 0E48.
-/

@[expose] public section

set_option autoImplicit false

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem map_iso_app_congr
    {C D E : Type*} [Category C] [Category D] [Category E]
    (H : D ⥤ E) {F G : C ⥤ D} {a b : F ≅ G} (h : a = b) (N : C) :
    H.map (a.hom.app N) = H.map (b.hom.app N) := by
  cases h
  rfl

private theorem two_prefix_congr
    {C : Type*} [Category C] {U V W T : C}
    {a : U ⟶ V} {b : V ⟶ W} {c d : W ⟶ T}
    (h : c = d) : a ≫ b ≫ c = a ≫ b ≫ d := by
  cases h
  rfl

private theorem morphism_comp_congr
    {C : Type*} [Category C] {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : f = f') (hg : g = g') : f ≫ g = f' ≫ g' := by
  cases hf
  cases hg
  rfl

private theorem chain_endpoint_transport
    {C : Type*} [Category C] {W U V S T : C}
    {a : W ⟶ U} {b : U ⟶ V} {e e' : V ⟶ S}
    {t t' : W ⟶ T} {p p' : T ⟶ S}
    (he : e = e') (ht : t = t') (hp : p = p')
    (h : a ≫ b ≫ e' = t' ≫ p') : a ≫ b ≫ e = t ≫ p := by
  rw [he, ht, hp]
  exact h

private theorem tensor_map_congr
    {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) {X Y : C} {f g : X ⟶ Y} (h : f = g) (K : D) :
    (T.map f).app K = (T.map g).app K := congrArg (fun w ↦ (T.map w).app K) h

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α) =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private theorem fixed_tensor_mate
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    {F : C ⥤ E} {R : E ⥤ C} {G : D ⥤ B} {S : B ⥤ D}
    (adj : F ⊣ R) (adj' : G ⊣ S)
    (J : C ⥤ D) (I : E ⥤ B)
    (TC : C ⥤ C) (TD : D ⥤ D) (TE : E ⥤ E) (TB : B ⥤ B)
    (e : J ⋙ G ⟶ F ⋙ I)
    (tf : TC ⋙ F ⟶ F ⋙ TE) (tg : TD ⋙ G ⟶ G ⋙ TB)
    (tj : J ⋙ TD ⟶ TC ⋙ J) (ti : I ⋙ TB ⟶ TE ⋙ I)
    (hc : ∀ N : C,
      G.map (tj.app N) ≫ e.app (TC.obj N) ≫ I.map (tf.app N) =
        tg.app (J.obj N) ≫ TB.map (e.app N) ≫ ti.app (F.obj N))
    (M : E) :
    let ex := (mateEquiv adj adj' (TwoSquare.mk J F G I e))
    let pf := (mateEquiv adj adj (TwoSquare.mk TC F F TE tf))
    let pg := (mateEquiv adj' adj' (TwoSquare.mk TD G G TB tg))
    tj.app (R.obj M) ≫ J.map (pf.app M) ≫ ex.app (TE.obj M) =
      TD.map (ex.app M) ≫ pg.app (I.obj M) ≫ S.map (ti.app M) := by
  intro ex pf pg
  have he (N : E) : G.map (ex.app N) ≫ adj'.counit.app (I.obj N) =
      e.app (R.obj N) ≫ I.map (adj.counit.app N) :=
    mateEquiv_counit adj adj' (TwoSquare.mk J F G I e) N
  have hf : F.map (pf.app M) ≫ adj.counit.app (TE.obj M) =
      tf.app (R.obj M) ≫ TE.map (adj.counit.app M) :=
    mateEquiv_counit adj adj (TwoSquare.mk TC F F TE tf) M
  have hg : G.map (pg.app (I.obj M)) ≫ adj'.counit.app (TB.obj (I.obj M)) =
      tg.app (S.obj (I.obj M)) ≫ TB.map (adj'.counit.app (I.obj M)) :=
    mateEquiv_counit adj' adj' (TwoSquare.mk TD G G TB tg) (I.obj M)
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [he]
  have hn := e.naturality (pf.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn, ← I.map_comp, hf, I.map_comp]
  have hn' := adj'.counit.naturality (ti.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn'
  rw [hn', reassoc_of% hg]
  have ht := tg.naturality (ex.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ht
  rw [reassoc_of% ht, ← TB.map_comp_assoc, he, TB.map_comp]
  rw [reassoc_of% (hc (R.obj M))]
  have hi := ti.naturality (adj.counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hi
  simp only [Category.assoc]
  rw [hi]

private theorem right_projection_mate
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {R : D ⥤ C}
    (adj : F ⊣ R) (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    (φ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U)
    (K : C) (M : D) :
    (mateEquiv adj adj (TwoSquare.mk (T.flip.obj K) F F (U.flip.obj (F.obj K))
      (((flipFunctor _ _ _).map φ).app K))).app M =
      ((adj.rightAdjointProjectionMap φ).app M).app K := by
  simp [mateEquiv_apply, TwoSquare.mk, flipFunctor, Functor.flip,
    Adjunction.rightAdjointProjectionMap_app_app, Adjunction.homEquiv_unit,
    Functor.map_comp]

private theorem tensor_tower_paste
    {C D E P Q Z : Type*}
    [Category C] [Category D] [Category E] [Category P] [Category Q] [Category Z]
    (j : C ⥤ D) (q : D ⥤ E) (i : E ⥤ Q) (b : D ⥤ P)
    (p : P ⥤ Q) (s : Q ⥤ Z) (r : P ⥤ Z) (a : C ⥤ P)
    (TC : C ⥤ C) (TD : D ⥤ D) (TE : E ⥤ E)
    (TP : P ⥤ P) (TQ : Q ⥤ Q) (TZ : Z ⥤ Z)
    (tj : j ⋙ TD ⟶ TC ⋙ j) (tq : q ⋙ TE ⟶ TD ⋙ q)
    (ti : i ⋙ TQ ⟶ TE ⋙ i) (ts : s ⋙ TZ ⟶ TQ ⋙ s)
    (tb : b ⋙ TP ⟶ TD ⋙ b) (tp : p ⋙ TQ ⟶ TP ⋙ p)
    (tr : r ⋙ TZ ⟶ TP ⋙ r) (ta : a ⋙ TP ⟶ TC ⋙ a)
    (ex : q ⋙ i ⟶ b ⋙ p) (beta : p ⋙ s ⟶ r) (omega : j ⋙ b ⟶ a)
    (hm : ∀ M, ti.app (q.obj M) ≫ i.map (tq.app M) ≫ ex.app (TD.obj M) =
      TQ.map (ex.app M) ≫ tp.app (b.obj M) ≫ p.map (tb.app M))
    (hp : ∀ M, TZ.map (beta.app M) ≫ tr.app M =
      ts.app (p.obj M) ≫ s.map (tp.app M) ≫ beta.app (TP.obj M))
    (ho : ∀ M, TP.map (omega.app M) ≫ ta.app M =
      tb.app (j.obj M) ≫ b.map (tj.app M) ≫ omega.app (TC.obj M))
    (M : C)
    (θ : TZ.obj (r.obj (a.obj M)) ⟶ r.obj (a.obj (TC.obj M)))
    (hθ : tr.app (a.obj M) ≫ r.map (ta.app M) = θ) :
    ts.app (i.obj (q.obj (j.obj M))) ≫ s.map (ti.app (q.obj (j.obj M))) ≫
        s.map (i.map (tq.app (j.obj M))) ≫ s.map (i.map (q.map (tj.app M))) ≫
        s.map (ex.app (j.obj (TC.obj M))) ≫ beta.app (b.obj (j.obj (TC.obj M))) ≫
        r.map (omega.app (TC.obj M)) =
      TZ.map (s.map (ex.app (j.obj M)) ≫ beta.app (b.obj (j.obj M)) ≫
        r.map (omega.app M)) ≫ θ := by
  rw [← hθ]
  have hn := ex.naturality (tj.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  have hns := congrArg s.map hn
  simp only [Functor.map_comp] at hns
  rw [reassoc_of% hns]
  have hms := congrArg s.map (hm (j.obj M))
  simp only [Functor.map_comp] at hms
  rw [reassoc_of% hms]
  have hs := ts.naturality (ex.app (j.obj M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs
  rw [← reassoc_of% hs]
  have hb := beta.naturality (tb.app (j.obj M) ≫ b.map (tj.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  simp only [Functor.map_comp, Category.assoc] at hb
  rw [reassoc_of% hb, ← reassoc_of% (hp (b.obj (j.obj M)))]
  have hos := congrArg r.map (ho M)
  simp only [Functor.map_comp] at hos
  rw [← hos]
  have hr := tr.naturality (omega.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hr
  rw [← reassoc_of% hr]
  simp only [Functor.map_comp, Category.assoc]

private theorem pullback_path_paste
    {C : Type*} [Category C] {A B D E F G H I J K : C}
    (a₀ : A ⟶ B) (a₁ : B ⟶ D) (a₂ : D ⟶ E) (a₃ : E ⟶ F) (a₄ : F ⟶ G)
    (b₁ : B ⟶ H) (b₂ : H ⟶ E) (c₁ : A ⟶ I)
    (d₁ : H ⟶ J) (d₂ : J ⟶ F) (e₁ : J ⟶ K) (t : I ⟶ K)
    (b : I ≅ H) (c : K ≅ G)
    (h₁ : a₁ ≫ a₂ = b₁ ≫ b₂) (h₂ : a₀ ≫ b₁ = c₁ ≫ b.hom)
    (h₃ : b₂ ≫ a₃ = d₁ ≫ d₂) (h₄ : d₂ ≫ a₄ = e₁ ≫ c.hom)
    (h₅ : d₁ ≫ e₁ = b.inv ≫ t) :
    a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ c.inv = c₁ ≫ t := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄]
  simp only [c.hom_inv_id, Category.comp_id]
  rw [h₅]
  simp only [b.hom_inv_id_assoc]

private theorem paste_right_naturality
    {C : Type*} [Category C] {W X Y Z U V T : C}
    {a : W ⟶ X} {b : X ⟶ Y} {c : Y ⟶ Z} {d : X ⟶ U} {e : U ⟶ Z}
    {f : Z ⟶ V} {g : U ⟶ T} {h : T ⟶ V} {i : W ⟶ T}
    (h₁ : b ≫ c = d ≫ e) (h₂ : e ≫ f = g ≫ h) (h₃ : a ≫ d ≫ g = i) :
    a ≫ b ≫ c ≫ f = i ≫ h := by
  calc
    _ = a ≫ (b ≫ c) ≫ f := by simp only [Category.assoc]
    _ = a ≫ d ≫ (e ≫ f) := by rw [h₁]; simp only [Category.assoc]
    _ = (a ≫ d ≫ g) ≫ h := by rw [h₂]; simp only [Category.assoc]
    _ = _ := by rw [h₃]

private theorem projection_coefficient_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {T : C ⥤ C} {U : D ⥤ D} {L : D ⥤ C}
    {Y Y' : D} {N N' : C} {W : E}
    {c : Y ⟶ Y'} {v : L.obj Y' ⟶ N'} {w : L.obj Y ⟶ N} {d : N ⟶ N'}
    {a : U.obj Y ⟶ F.obj (T.obj (L.obj Y))}
    {a' : U.obj Y' ⟶ F.obj (T.obj (L.obj Y'))}
    (ha : U.map c ≫ a' = a ≫ F.map (T.map (L.map c)))
    (hv : L.map c ≫ v = w ≫ d) (p : W ⟶ G.obj (U.obj Y)) :
    p ≫ G.map (U.map c) ≫ G.map a' ≫ G.map (F.map (T.map v)) =
      p ≫ G.map a ≫ G.map (F.map (T.map w)) ≫ G.map (F.map (T.map d)) := by
  have h := congrArg G.map ha
  have hν := congrArg (fun z ↦ G.map (F.map (T.map z))) hv
  simp only [Functor.map_comp] at h hν
  rw [reassoc_of% h, hν]

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor leftDerivedUpperStarTensorComparison

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

private noncomputable def towerOpen
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    e.restrict.Z ⟶ e.Z := pullback.fst e.g d.i

private theorem towerSquare
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    IsPullback e.restrict.g (towerOpen d e) d.i e.g := e.isPullback_restrict

private theorem towerOpen_isOpen
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    IsOpenImmersion (towerOpen d e) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsOpenImmersion) (towerSquare d e) inferInstance

private theorem towerOpen_comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    e.restrict.i ≫ towerOpen d e = e.i := e.restrict_i_fst

attribute [local instance] towerOpen_isOpen
attribute [local irreducible] towerOpen

section Generic
set_option backward.defeqAttrib.useBackward true

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
  {FC : B → B → Type*} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

omit [UpperStarPreservesFlat B] in
private theorem open_exchange_mate
    {U V W Z : Scheme.{u}} {q : U ⟶ W} {b : U ⟶ V} {i : W ⟶ Z} {p : V ⟶ Z}
    [IsOpenImmersion i] [IsOpenImmersion b] (sq : IsPullback q b i p) :
    let J := (openImmersionLowerShriek B i).mapDerivedCategory
    let I := (openImmersionLowerShriek B b).mapDerivedCategory
    let F := (upperStar B q).leftDerivedFunctor
    let G := (upperStar B p).leftDerivedFunctor
    openImmersionLowerShriekLowerStarExchange B sq =
      (mateEquiv (derivedUpperStarLowerStarAdjunction B q)
        (derivedUpperStarLowerStarAdjunction B p)
        (TwoSquare.mk J F G I (derivedOpenImmersionLowerShriekBaseChangeIso B sq).inv)) :=
          by
  dsimp only
  unfold openImmersionLowerShriekLowerStarExchange
  rw [
    mapDerivedUpperStarLowerStarAdjunction_eq B q,
    mapDerivedUpperStarLowerStarAdjunction_eq B p, mate_ofNatIsoLeft]
  apply congrArg (fun α ↦
    (mateEquiv (derivedUpperStarLowerStarAdjunction B q)
      (derivedUpperStarLowerStarAdjunction B p) α))
  ext K
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk,
    
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]

private theorem mixed_projection
    {U V W Z : Scheme.{u}} {q : U ⟶ W} {b : U ⟶ V} {i : W ⟶ Z} {p : V ⟶ Z}
    [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback q b i p)
    (M : DerivedCategory (Sheaf U.smallEtaleTopology B)) (N : DerivedCategory (Sheaf
      Z.smallEtaleTopology B)) :
    let J := (openImmersionLowerShriek B i).mapDerivedCategory
    let I := (openImmersionLowerShriek B b).mapDerivedCategory
    let R := (lowerStar B (q)).rightDerivedFunctor
    let S := (lowerStar B (p)).rightDerivedFunctor
    let F := (upperStar B q).leftDerivedFunctor
    let G := (upperStar B p).leftDerivedFunctor
    let L := (upperStar B i).leftDerivedFunctor
    let T := derivedTensor B U
    let U' := derivedTensor B Z
    let ex := openImmersionLowerShriekLowerStarExchange B sq
    ((derivedOpenImmersionLowerShriekProjectionIso B i).inv.app (R.obj M)).app N ≫
        J.map (((rightDerivedLowerStarProjectionMap B q).app M).app (L.obj N)) ≫
        ex.app ((T.obj M).obj (F.obj (L.obj N))) =
      (U'.map (ex.app M)).app N ≫
        ((rightDerivedLowerStarProjectionMap B p).app (I.obj M)).app N ≫
        S.map (((derivedOpenImmersionLowerShriekProjectionIso B b).inv.app M).app
          (G.obj N)) ≫
        S.map (I.map ((T.obj M).map ((derivedSquareUpperStarIso B sq.toCommSq).hom.app N))) := by
  let J := (openImmersionLowerShriek B i).mapDerivedCategory
  let I := (openImmersionLowerShriek B b).mapDerivedCategory
  let F := (upperStar B q).leftDerivedFunctor
  let G := (upperStar B p).leftDerivedFunctor
  let L := (upperStar B i).leftDerivedFunctor
  let T := derivedTensor B U
  let TW := derivedTensor B W
  let TV := derivedTensor B V
  let TZ := derivedTensor B Z
  let R := (lowerStar B (q)).rightDerivedFunctor
  let S := (lowerStar B (p)).rightDerivedFunctor
  let TC := TW.flip.obj (L.obj N)
  let TD := TZ.flip.obj N
  let TE := T.flip.obj (F.obj (L.obj N))
  let TB := TV.flip.obj (G.obj N)
  let e := (derivedOpenImmersionLowerShriekBaseChangeIso B sq).inv
  let tf : TC ⋙ F ⟶ F ⋙ TE :=
    ((flipFunctor _ _ _).map (leftDerivedUpperStarTensorComparison B q)).app (L.obj N)
  let tg : TD ⋙ G ⟶ G ⋙ TB :=
    ((flipFunctor _ _ _).map (leftDerivedUpperStarTensorComparison B p)).app N
  let tj : J ⋙ TD ⟶ TC ⋙ J :=
    ((flipFunctor _ _ _).map (derivedOpenImmersionLowerShriekProjectionIso B i).inv).app N
  let ti : I ⋙ TB ⟶ TE ⋙ I :=
    ((flipFunctor _ _ _).map (derivedOpenImmersionLowerShriekProjectionIso B b).inv).app
        (G.obj N) ≫
      Functor.whiskerRight (T.flip.map
        ((derivedSquareUpperStarIso B sq.toCommSq).hom.app N)) I
  have hc (K : DerivedCategory (Sheaf W.smallEtaleTopology B)) :
      G.map (tj.app K) ≫ e.app (TC.obj K) ≫ I.map (tf.app K) =
        tg.app (J.obj K) ≫ TB.map (e.app K) ≫ ti.app (F.obj K) := by
    let φp := leftDerivedUpperStarTensorIso B p (J.obj K) N
    let φq := leftDerivedUpperStarTensorIso B q K (L.obj N)
    have h := congrArg (fun t ↦ φp.hom ≫ t ≫ I.map φq.hom)
      (derivedOpenImmersionLowerShriekProjectionIso_inv_baseChange B sq K N)
    have hq : I.map φq.inv ≫ I.map φq.hom = 𝟙 _ := by
      rw [← I.map_comp, φq.inv_hom_id, I.map_id]
    change φp.hom ≫ (φp.inv ≫ _ ≫ _) ≫ I.map φq.hom =
      φp.hom ≫ (_ ≫ _ ≫ _ ≫ I.map φq.inv) ≫ I.map φq.hom at h
    simp only [Category.assoc, φp.hom_inv_id_assoc, hq, Category.comp_id] at h
    simpa only [φp, φq, tj, ti, tf, tg, e, TC, TD, TE, TB, flipFunctor,
      Functor.flip, NatTrans.comp_app, Functor.whiskerRight_app,
      leftDerivedUpperStarTensorIso_hom, Category.assoc] using h
  have h := fixed_tensor_mate (derivedUpperStarLowerStarAdjunction B q)
    (derivedUpperStarLowerStarAdjunction B p) J I TC TD TE TB e tf tg tj ti hc M
  have he := open_exchange_mate B sq
  dsimp only at he
  have hpq :
      (mateEquiv (derivedUpperStarLowerStarAdjunction B q)
        (derivedUpperStarLowerStarAdjunction B q)
        (TwoSquare.mk TC F F TE tf)).app M =
      ((rightDerivedLowerStarProjectionMap B q).app M).app (L.obj N) := by
    exact right_projection_mate (derivedUpperStarLowerStarAdjunction B q) TW T
      (leftDerivedUpperStarTensorComparison B q) (L.obj N) M
  have hpp :
      (mateEquiv (derivedUpperStarLowerStarAdjunction B p)
        (derivedUpperStarLowerStarAdjunction B p)
        (TwoSquare.mk TD G G TB tg)).app (I.obj M) =
      ((rightDerivedLowerStarProjectionMap B p).app (I.obj M)).app N := by
    exact right_projection_mate (derivedUpperStarLowerStarAdjunction B p) TZ TV
      (leftDerivedUpperStarTensorComparison B p) N (I.obj M)
  dsimp only at h ⊢
  rw [hpq, hpp, ← he] at h
  simp only [tj, ti, TD, TE, flipFunctor, Functor.flip,
    Functor.map_comp, NatTrans.comp_app, Functor.whiskerRight_app] at h
  exact h

set_option backward.isDefEq.respectTransparency true
attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] Compactification.restrict Compactification.ofIsPullback
  Compactification.comp Compactification.copy Compactification.postcomp

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor projectionMapOfCompactification
  derivedOpenImmersionLowerShriekProjectionIso rightDerivedLowerStarComp

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  openImmersionLowerShriek upperStar lowerStar

attribute [local irreducible] rightDerivedLowerStarProjectionMap
  openImmersionLowerShriekLowerStarExchange
  mapDerivedCategoryOpenImmersionLowerShriekComp mapDerivedCategoryOpenImmersionLowerShriekCongr

attribute [local irreducible] leftDerivedUpperStarComp derivedSquareUpperStarIso
  leftDerivedUpperStarCompactificationIso

omit [HasSmallSiteSheafify B] in
private noncomputable def openStrength
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    {P : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (v : (upperStar B j).leftDerivedFunctor.obj N ⟶ P) :
    (openImmersionLowerShriek B j).mapDerivedCategory ⋙ (derivedTensor B Y).flip.obj N ⟶
      (derivedTensor B X).flip.obj P ⋙ (openImmersionLowerShriek B j).mapDerivedCategory :=
  ((flipFunctor _ _ _).map (derivedOpenImmersionLowerShriekProjectionIso B j).inv).app N ≫
    Functor.whiskerRight ((derivedTensor B X).flip.map v)
      (openImmersionLowerShriek B j).mapDerivedCategory

omit [HasSmallSiteSheafify B] in
private theorem openStrength_app
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    {P : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (v : (upperStar B j).leftDerivedFunctor.obj N ⟶ P)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (openStrength B j N v).app M =
      ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).app N ≫
        (openImmersionLowerShriek B j).mapDerivedCategory.map
          (((derivedTensor B X).obj M).map v) := rfl

omit [HasSmallSiteSheafify B] in
private noncomputable def properStrength
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (lowerStar B q).rightDerivedFunctor ⋙ (derivedTensor B Y).flip.obj N ⟶
      (derivedTensor B X).flip.obj ((upperStar B q).leftDerivedFunctor.obj N) ⋙
        (lowerStar B q).rightDerivedFunctor :=
  ((flipFunctor _ _ _).map (rightDerivedLowerStarProjectionMap B q)).app N

omit [HasSmallSiteSheafify B] in
private theorem properStrength_app
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (properStrength B q N).app M =
      ((rightDerivedLowerStarProjectionMap B q).app M).app N := rfl

omit [HasSmallSiteSheafify B] in
private noncomputable def properTwistedStrength
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    {P : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (v : (upperStar B q).leftDerivedFunctor.obj N ⟶ P) :
    (lowerStar B q).rightDerivedFunctor ⋙ (derivedTensor B Y).flip.obj N ⟶
      (derivedTensor B X).flip.obj P ⋙ (lowerStar B q).rightDerivedFunctor :=
  properStrength B q N ≫ Functor.whiskerRight ((derivedTensor B X).flip.map v)
    (lowerStar B q).rightDerivedFunctor

omit [HasSmallSiteSheafify B] in
private theorem properTwistedStrength_app
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (N : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    {P : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (v : (upperStar B q).leftDerivedFunctor.obj N ⟶ P)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (properTwistedStrength B q N v).app M =
      ((rightDerivedLowerStarProjectionMap B q).app M).app N ≫
        (lowerStar B q).rightDerivedFunctor.map (((derivedTensor B X).obj M).map v) := rfl

omit [HasSmallSiteSheafify B] in
private theorem openProjection_naturality_right
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (N N' : DerivedCategory (Sheaf Y.smallEtaleTopology B)) (v : N ⟶ N') :
    ((derivedTensor B Y).obj
        ((openImmersionLowerShriek B j).mapDerivedCategory.obj M)).map v ≫
        ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).app N' =
      ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).app N ≫
        (openImmersionLowerShriek B j).mapDerivedCategory.map
          (((derivedTensor B X).obj M).map ((upperStar B j).leftDerivedFunctor.map v)) := by
  exact ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).naturality v

omit [HasSmallSiteSheafify B] in
private theorem properProjection_naturality_right
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (N N' : DerivedCategory (Sheaf Y.smallEtaleTopology B)) (v : N ⟶ N') :
    ((derivedTensor B Y).obj ((lowerStar B q).rightDerivedFunctor.obj M)).map v ≫
        ((rightDerivedLowerStarProjectionMap B q).app M).app N' =
      ((rightDerivedLowerStarProjectionMap B q).app M).app N ≫
        (lowerStar B q).rightDerivedFunctor.map
          (((derivedTensor B X).obj M).map ((upperStar B q).leftDerivedFunctor.map v)) := by
  exact ((rightDerivedLowerStarProjectionMap B q).app M).naturality v

attribute [local irreducible] openStrength properStrength properTwistedStrength

private theorem mixed_twisted_projection
    {U V W Z : Scheme.{u}} {q : U ⟶ W} {b : U ⟶ V} {i : W ⟶ Z} {p : V ⟶ Z}
    [IsOpenImmersion i] [IsOpenImmersion b]
    (sq : IsPullback q b i p)
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology B))
    (P : DerivedCategory (Sheaf W.smallEtaleTopology B))
    (v : (upperStar B i).leftDerivedFunctor.obj N ⟶ P)
    (M : DerivedCategory (Sheaf U.smallEtaleTopology B)) :
    (openStrength B i N v).app ((lowerStar B q).rightDerivedFunctor.obj M) ≫
      (openImmersionLowerShriek B i).mapDerivedCategory.map
        ((properStrength B q P).app M) ≫
      (openImmersionLowerShriekLowerStarExchange B sq).app
        (((derivedTensor B U).flip.obj ((upperStar B q).leftDerivedFunctor.obj P)).obj M) =
    ((derivedTensor B Z).flip.obj N).map
        ((openImmersionLowerShriekLowerStarExchange B sq).app M) ≫
      (properStrength B p N).app ((openImmersionLowerShriek B b).mapDerivedCategory.obj M) ≫
      (lowerStar B p).rightDerivedFunctor.map
        ((openStrength B b ((upperStar B p).leftDerivedFunctor.obj N)
          ((derivedSquareUpperStarIso B sq.toCommSq).hom.app N ≫
            (upperStar B q).leftDerivedFunctor.map v)).app M) := by
  have h0 := mixed_projection B sq M N
  dsimp only at h0
  have hq := properProjection_naturality_right B q M _ _ v
  have hqi := congrArg (openImmersionLowerShriek B i).mapDerivedCategory.map hq
  simp only [Functor.map_comp] at hqi
  have he := (openImmersionLowerShriekLowerStarExchange B sq).naturality
    (((derivedTensor B U).obj M).map ((upperStar B q).leftDerivedFunctor.map v))
  dsimp only [Functor.comp_map, Functor.comp_obj] at he
  have hh := paste_right_naturality hqi he h0
  simpa only [openStrength_app, properStrength_app, Functor.flip_obj_obj,
    Functor.flip_obj_map, Functor.flip_map_app, Functor.map_comp, Category.assoc] using hh

omit [HasSmallSiteSheafify B] in
private theorem openStrength_transport
    {X V Z : Scheme.{u}} (j : X ⟶ V) [IsOpenImmersion j] (q : V ⟶ Z)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (N : DerivedCategory (Sheaf Z.smallEtaleTopology B))
    (N' : DerivedCategory (Sheaf V.smallEtaleTopology B))
    (c : (upperStar B q).leftDerivedFunctor.obj N ⟶ N')
    {P P' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (v : (upperStar B j).leftDerivedFunctor.obj N' ⟶ P')
    (w : (upperStar B j).leftDerivedFunctor.obj
      ((upperStar B q).leftDerivedFunctor.obj N) ⟶ P)
    (d : P ⟶ P')
    (hv : (upperStar B j).leftDerivedFunctor.map c ≫ v = w ≫ d) :
    (properTwistedStrength B q N c).app
        ((openImmersionLowerShriek B j).mapDerivedCategory.obj M) ≫
      (lowerStar B q).rightDerivedFunctor.map ((openStrength B j N' v).app M) =
    ((rightDerivedLowerStarProjectionMap B q).app
        ((openImmersionLowerShriek B j).mapDerivedCategory.obj M)).app N ≫
      (lowerStar B q).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).app
          ((upperStar B q).leftDerivedFunctor.obj N)) ≫
      (lowerStar B q).rightDerivedFunctor.map
        ((openImmersionLowerShriek B j).mapDerivedCategory.map
          (((derivedTensor B X).obj M).map w)) ≫
      (lowerStar B q).rightDerivedFunctor.map
        ((openImmersionLowerShriek B j).mapDerivedCategory.map
          (((derivedTensor B X).obj M).map d)) := by
  simp only [properTwistedStrength_app, openStrength_app,
    Functor.map_comp, Category.assoc]
  exact projection_coefficient_transport
    (F := (openImmersionLowerShriek B j).mapDerivedCategory)
    (G := (lowerStar B q).rightDerivedFunctor)
    (T := (derivedTensor B X).obj M)
    (U := (derivedTensor B V).obj
      ((openImmersionLowerShriek B j).mapDerivedCategory.obj M))
    (L := (upperStar B j).leftDerivedFunctor)
    (openProjection_naturality_right B j M _ _ c) hv
    (((rightDerivedLowerStarProjectionMap B q).app
      ((openImmersionLowerShriek B j).mapDerivedCategory.obj M)).app N)

omit [HasSmallSiteSheafify B] in
private theorem properStrength_comp
    {P Q Z : Scheme.{u}} (q : P ⟶ Q) (s : Q ⟶ Z)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology B)) : ∀ N, ((derivedTensor B Z).flip.obj K).map
      (((rightDerivedLowerStarComp B q s).hom).app N) ≫ (properTwistedStrength B (q ≫ s) K
      ((leftDerivedUpperStarComp B q s).hom.app K)).app N =
    (properStrength B s K).app (((lowerStar B (q)).rightDerivedFunctor).obj N) ≫ ((lowerStar B
      (s)).rightDerivedFunctor).map ((properStrength B q (((upperStar B s).leftDerivedFunctor).obj
      K)).app N) ≫ ((rightDerivedLowerStarComp B q s).hom).app (((derivedTensor B P).flip.obj
      (((upperStar B q).leftDerivedFunctor).obj (((upperStar B s).leftDerivedFunctor).obj K))).obj
      N) := by
  intro N
  have h := rightDerivedLowerStarProjectionMap_comp B q s (q ≫ s) rfl N K
  have hb : (rightDerivedLowerStarComp B q s).hom =
      rightDerivedLowerStarCompHom B q s (q ≫ s) rfl := by
    rw [rightDerivedLowerStarCompHom, conjugateEquiv_leftDerivedUpperStarComp_hom]
    unfold rightDerivedLowerStarComp
    rfl
  rw [← hb] at h
  simpa only [openStrength_app, properStrength_app, properTwistedStrength_app,
    flipFunctor_map_app_app, Functor.flip_obj_obj,
    Functor.flip_obj_map, Functor.flip_map_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_obj,
    Functor.comp_map, Category.assoc] using h

omit [HasSmallSiteSheafify B] in
private theorem openStrength_comp
    {X V P : Scheme.{u}} (j : X ⟶ V) (b : V ⟶ P) (a : X ⟶ P)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion a]
    (hoc : j ≫ b = a)
    (N : DerivedCategory (Sheaf P.smallEtaleTopology B))
    (N' : DerivedCategory (Sheaf V.smallEtaleTopology B))
    (N'' : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (v : (upperStar B b).leftDerivedFunctor.obj N ⟶ N')
    (w : (upperStar B j).leftDerivedFunctor.obj N' ⟶ N'') : ∀ M, ((derivedTensor B P).flip.obj
      N).map (((mapDerivedCategoryOpenImmersionLowerShriekComp B j b).symm ≪≫
  mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom.app M) ≫ (openStrength B a N
    ((leftDerivedUpperStarComp B j b a hoc.symm).hom.app
    N ≫ ((upperStar B j).leftDerivedFunctor).map v ≫ w)).app M =
    (openStrength B b N v).app (((openImmersionLowerShriek B j).mapDerivedCategory).obj M) ≫
      ((openImmersionLowerShriek B b).mapDerivedCategory).map ((openStrength B j N' w).app M) ≫
      ((mapDerivedCategoryOpenImmersionLowerShriekComp B j b).symm ≪≫
  mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom.app (((derivedTensor B X).flip.obj
    N'').obj M) := by
  intro M
  have h0 := derivedOpenImmersionLowerShriekProjectionIso_inv_comp B j b a
    hoc M N
  dsimp only at h0
  have he := ((mapDerivedCategoryOpenImmersionLowerShriekComp B j b).symm ≪≫
  mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom.naturality (((derivedTensor B X).obj
    M).map (((upperStar B j).leftDerivedFunctor).map v ≫ w))
  dsimp only [openStrength_app, properStrength_app, properTwistedStrength_app, Functor.comp_map,
    Functor.comp_obj] at he
  simp only [Functor.map_comp, Category.assoc] at he
  have hj := ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).naturality v
  have hjD := congrArg ((openImmersionLowerShriek B b).mapDerivedCategory).map hj
  simp only [Functor.map_comp] at hjD
  have h₁ := congrArg (fun z ↦ z ≫ ((openImmersionLowerShriek B a).mapDerivedCategory).map
    (((derivedTensor B X).obj M).map (((upperStar B j).leftDerivedFunctor).map v ≫ w))) h0
  have h₂ := congrArg (fun z ↦ (((derivedOpenImmersionLowerShriekProjectionIso B b).inv.app
    (((openImmersionLowerShriek B j).mapDerivedCategory).obj M)).app N) ≫ ((openImmersionLowerShriek
      B b).mapDerivedCategory).map (((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app
      M).app
    ((upperStar B b).leftDerivedFunctor.obj N)) ≫ z) he
  have h₃ := congrArg (fun z ↦ (((derivedOpenImmersionLowerShriekProjectionIso B b).inv.app
    (((openImmersionLowerShriek B j).mapDerivedCategory).obj M)).app N) ≫ z ≫
      ((openImmersionLowerShriek B b).mapDerivedCategory).map (((openImmersionLowerShriek B
      j).mapDerivedCategory).map (((derivedTensor B X).obj M).map w)) ≫
    ((mapDerivedCategoryOpenImmersionLowerShriekComp B j b).symm ≪≫
  mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom.app (((derivedTensor B X).flip.obj
    N'').obj M)) hjD
  simp only [Functor.map_comp, Category.assoc] at h₁ h₂ h₃
  have hh := h₁.trans (h₂.symm.trans h₃.symm)
  simp only [openStrength_app, Functor.flip_obj_obj, Functor.flip_obj_map]
  set_option backward.isDefEq.respectTransparency true in
    simp only [Functor.map_comp, Category.assoc]
  set_option backward.isDefEq.respectTransparency true in
    exact hh

-- Elaborate the four pseudofunctor coherence identities at the stated objects.
omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
private theorem tower_pullback
    {X V Y P Q Z : Scheme.{u}}
    (j : X ⟶ V) (q : V ⟶ Y) (b : V ⟶ P) (p : P ⟶ Q)
    (i : Y ⟶ Q) (s : Q ⟶ Z) (a : X ⟶ P) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hjq : f = j ≫ q) (his : g = i ≫ s) (hjb : a = j ≫ b)
    (hap : f ≫ i = a ≫ p) (hsq : q ≫ i = b ≫ p)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology B)) :
    (upperStar B a).leftDerivedFunctor.map
        ((leftDerivedUpperStarComp B p s).hom.app K) ≫
      (leftDerivedUpperStarComp B j b a hjb).hom.app
        ((upperStar B p).leftDerivedFunctor.obj
          ((upperStar B s).leftDerivedFunctor.obj K)) ≫
      (upperStar B j).leftDerivedFunctor.map
        ((derivedSquareUpperStarIso B (CommSq.mk hsq)).hom.app
          ((upperStar B s).leftDerivedFunctor.obj K)) ≫
      (upperStar B j).leftDerivedFunctor.map
        ((upperStar B q).leftDerivedFunctor.map
          ((leftDerivedUpperStarComp B i s g his).inv.app K)) ≫
      (leftDerivedUpperStarComp B j q f hjq).inv.app
        ((upperStar B g).leftDerivedFunctor.obj K) =
      (leftDerivedUpperStarComp B a (p ≫ s) (f ≫ g)
        (by
          rw [his]
          exact (Category.assoc f i s).symm.trans
            ((congrArg (· ≫ s) hap).trans (Category.assoc a p s)))).inv.app K ≫
      (leftDerivedUpperStarComp B f g).hom.app K := by
  let N := (upperStar B s).leftDerivedFunctor.obj K
  let vd := (leftDerivedUpperStarComp B i s g his).inv.app K
  let bc := (leftDerivedUpperStarComp B (f ≫ i) s (f ≫ g)
    (by rw [his, Category.assoc])).app K
  let cc := (leftDerivedUpperStarComp B j q f hjq).app
    ((upperStar B g).leftDerivedFunctor.obj K)
  have h₁ := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    B j b p a (q ≫ i) (f ≫ i) hjb hsq hap N
  have h₂ := map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
    B a p s (f ≫ i) (p ≫ s) (f ≫ g) hap rfl (by rw [his, Category.assoc]) K
  have h₃ := leftDerivedUpperStarComp_assoc'_app
    B j q i f (q ≫ i) (f ≫ i) hjq rfl rfl N
  have h₄ := (leftDerivedUpperStarComp B j q f hjq).hom.naturality vd
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₄
  have h₅ := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    B f i s (f ≫ i) g (f ≫ g) rfl his (by rw [his, Category.assoc]) K
  have ht := pullback_path_paste
    ((upperStar B a).leftDerivedFunctor.map
      ((leftDerivedUpperStarComp B p s).hom.app K))
    ((leftDerivedUpperStarComp B j b a hjb).hom.app
      ((upperStar B p).leftDerivedFunctor.obj N))
    ((upperStar B j).leftDerivedFunctor.map
      ((leftDerivedUpperStarComp B b p (q ≫ i) hsq).inv.app N))
    ((upperStar B j).leftDerivedFunctor.map
      ((leftDerivedUpperStarComp B q i).hom.app N))
    ((upperStar B j).leftDerivedFunctor.map
      ((upperStar B q).leftDerivedFunctor.map vd))
    ((leftDerivedUpperStarComp B a p (f ≫ i) hap).inv.app N)
    ((leftDerivedUpperStarComp B j (q ≫ i) (f ≫ i)
      (by rw [hjq, Category.assoc])).hom.app N)
    ((leftDerivedUpperStarComp B a (p ≫ s) (f ≫ g)
      (by
        rw [his]
        exact (Category.assoc f i s).symm.trans
          ((congrArg (· ≫ s) hap).trans (Category.assoc a p s)))).inv.app K)
    ((leftDerivedUpperStarComp B f i).hom.app N)
    ((leftDerivedUpperStarComp B j q f hjq).hom.app
      ((upperStar B i).leftDerivedFunctor.obj N))
    ((upperStar B f).leftDerivedFunctor.map vd)
    ((leftDerivedUpperStarComp B f g).hom.app K)
    bc cc h₁ h₂ h₃ h₄.symm h₅
  simpa only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, N, vd, bc, cc, Iso.app_hom,
    Iso.app_inv, Category.assoc] using ht

omit [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B] in
private theorem towerModel_map
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    {N N' : DerivedCategory (Sheaf X.smallEtaleTopology B)} (v : N ⟶ N') :
    (rightDerivedLowerShriekOfCompactification B (d.comp e)).map v =
      ((openImmersionLowerShriek B e.i).mapDerivedCategory ⋙
        (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor).map v := by
  rfl

private theorem tower_projection
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (c : Compactification f) (b : c.Z ⟶ e.Z) [hb : IsOpenImmersion b]
    (sq : IsPullback c.g b d.i e.g) (hoc : c.i ≫ b = e.i)
    (hcomp : f ≫ g = e.i ≫ (e.g ≫ d.g))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology B)) :
    ((projectionMapOfCompactification B d).app ((rightDerivedLowerShriekOfCompactification B c).obj
      M)).app K ≫
        (rightDerivedLowerShriekOfCompactification B d).map (((projectionMapOfCompactification B
          c).app M).app (((upperStar B g).leftDerivedFunctor).obj K)) ≫
        (fun N : DerivedCategory (Sheaf X.smallEtaleTopology B) ↦
      ((lowerStar B d.g).rightDerivedFunctor).map ((openImmersionLowerShriekLowerStarExchange B
        sq).app (((openImmersionLowerShriek B c.i).mapDerivedCategory).obj N)) ≫
        (rightDerivedLowerStarComp B e.g d.g).hom.app (((openImmersionLowerShriek B
          b).mapDerivedCategory).obj (((openImmersionLowerShriek B c.i).mapDerivedCategory).obj
          N)) ≫
        ((lowerStar B (e.g ≫ d.g)).rightDerivedFunctor).map
          (((mapDerivedCategoryOpenImmersionLowerShriekComp B c.i
      b).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom.app N)) (((derivedTensor B X).obj
          M).obj (((upperStar B f).leftDerivedFunctor).obj (((upperStar B g).leftDerivedFunctor).obj
          K))) =
      ((derivedTensor B Z).map ((fun N : DerivedCategory (Sheaf X.smallEtaleTopology B) ↦
      ((lowerStar B d.g).rightDerivedFunctor).map ((openImmersionLowerShriekLowerStarExchange B
        sq).app (((openImmersionLowerShriek B c.i).mapDerivedCategory).obj N)) ≫
        (rightDerivedLowerStarComp B e.g d.g).hom.app (((openImmersionLowerShriek B
          b).mapDerivedCategory).obj (((openImmersionLowerShriek B c.i).mapDerivedCategory).obj
          N)) ≫
        ((lowerStar B (e.g ≫ d.g)).rightDerivedFunctor).map
          (((mapDerivedCategoryOpenImmersionLowerShriekComp B c.i
      b).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom.app N)) M)).app K ≫
        ((((rightDerivedLowerStarProjectionMap B (e.g ≫ d.g)).app
          ((openImmersionLowerShriek B e.i).mapDerivedCategory.obj M)).app K) ≫
        (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor.map
          (((derivedOpenImmersionLowerShriekProjectionIso B e.i).inv.app M).app
            ((upperStar B (e.g ≫ d.g)).leftDerivedFunctor.obj K)) ≫
        ((openImmersionLowerShriek B e.i).mapDerivedCategory ⋙
          (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor).map
          (((derivedTensor B X).obj M).map
            ((leftDerivedUpperStarComp B e.i (e.g ≫ d.g) (f ≫ g) hcomp).inv.app K))) ≫
        (((openImmersionLowerShriek B e.i).mapDerivedCategory ⋙
      (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor)).map (((derivedTensor B X).obj M).map
        ((leftDerivedUpperStarComp B f g).hom.app K)) := by
  set_option backward.isDefEq.respectTransparency true in
      dsimp only
      simp only [projectionMapOfCompactification_app_app, Functor.comp_map, Functor.comp_obj,
        Functor.map_comp, Category.assoc]
      have hm (N : DerivedCategory
          (Sheaf c.Z.smallEtaleTopology B)) :=
        mixed_twisted_projection B
          (U := c.Z) (V := e.Z) (W := Y) (Z := d.Z)
          (q := c.g) (b := b) (i := d.i) (p := e.g)
          sq
          ((upperStar B d.g).leftDerivedFunctor.obj K)
          ((upperStar B g).leftDerivedFunctor.obj K)
          ((leftDerivedUpperStarCompactificationIso B d).hom.app K) N
      have hp := properStrength_comp B e.g d.g K
      have ho := openStrength_comp B
        c.i b e.i hoc
        ((upperStar B e.g).leftDerivedFunctor.obj
          ((upperStar B d.g).leftDerivedFunctor.obj K))
        ((upperStar B c.g).leftDerivedFunctor.obj
          ((upperStar B g).leftDerivedFunctor.obj K))
        ((upperStar B f).leftDerivedFunctor.obj
          ((upperStar B g).leftDerivedFunctor.obj K))
        ((derivedSquareUpperStarIso B
          sq.toCommSq).hom.app
            ((upperStar B d.g).leftDerivedFunctor.obj K) ≫
          (upperStar B c.g).leftDerivedFunctor.map
            ((leftDerivedUpperStarCompactificationIso B d).hom.app K))
        ((leftDerivedUpperStarCompactificationIso
          B c).hom.app
            ((upperStar B g).leftDerivedFunctor.obj K))
      have htau : ((upperStar B e.i).leftDerivedFunctor).map ((leftDerivedUpperStarComp B e.g
        d.g (e.g ≫ d.g) rfl).hom.app K) ≫ ((leftDerivedUpperStarComp B c.i b e.i
        hoc.symm).hom.app
          (((upperStar B e.g).leftDerivedFunctor).obj (((upperStar B
            d.g).leftDerivedFunctor).obj K)) ≫ ((upperStar B c.i).leftDerivedFunctor).map
            (((derivedSquareUpperStarIso B sq.toCommSq).hom.app (((upperStar B
            d.g).leftDerivedFunctor).obj K)) ≫ ((upperStar B c.g).leftDerivedFunctor).map
            ((leftDerivedUpperStarCompactificationIso B d).hom.app K)) ≫
            ((leftDerivedUpperStarCompactificationIso B c).hom.app (((upperStar B
            g).leftDerivedFunctor).obj K))) =
          (leftDerivedUpperStarComp B e.i (e.g ≫ d.g) (f ≫ g) hcomp).inv.app K ≫
            (leftDerivedUpperStarComp B f g (f ≫ g) rfl).hom.app K := by
        have h := tower_pullback B c.i c.g b e.g d.i d.g e.i f g c.comm d.comm
          hoc.symm e.comm sq.w K
        simpa only [
          leftDerivedUpperStarCompactificationIso_eq, Iso.symm_hom,
          Compactification.comp_Z, Compactification.comp_i, Compactification.comp_g,
            Functor.map_comp,
          Category.assoc] using h
      have hstrength := openStrength_transport B
        e.i (e.g ≫ d.g) M K
        ((upperStar B e.g).leftDerivedFunctor.obj
          ((upperStar B d.g).leftDerivedFunctor.obj K))
        ((leftDerivedUpperStarComp B e.g d.g
          (e.g ≫ d.g) rfl).hom.app K)
        ((leftDerivedUpperStarComp B c.i b
          e.i hoc.symm).hom.app
            ((upperStar B e.g).leftDerivedFunctor.obj
              ((upperStar B d.g).leftDerivedFunctor.obj K)) ≫
          (upperStar B c.i).leftDerivedFunctor.map
            ((derivedSquareUpperStarIso B
              sq.toCommSq).hom.app
                ((upperStar B d.g).leftDerivedFunctor.obj K) ≫
              (upperStar B c.g).leftDerivedFunctor.map
                ((leftDerivedUpperStarCompactificationIso
                  B d).hom.app K)) ≫
          (leftDerivedUpperStarCompactificationIso B
            c).hom.app
              ((upperStar B g).leftDerivedFunctor.obj K))
        ((leftDerivedUpperStarComp B e.i (e.g ≫ d.g)
          (f ≫ g) hcomp).inv.app K)
        ((leftDerivedUpperStarComp B f g (f ≫ g) rfl).hom.app K)
        htau
      have hfinal := tensor_tower_paste
        ((openImmersionLowerShriek B c.i).mapDerivedCategory)
        ((lowerStar B c.g).rightDerivedFunctor)
        ((openImmersionLowerShriek B d.i).mapDerivedCategory)
        ((openImmersionLowerShriek B b).mapDerivedCategory)
        ((lowerStar B e.g).rightDerivedFunctor)
        ((lowerStar B d.g).rightDerivedFunctor)
        ((lowerStar B (e.g ≫ d.g)).rightDerivedFunctor)
        ((openImmersionLowerShriek B e.i).mapDerivedCategory)
        ((derivedTensor B X).flip.obj (((upperStar B f).leftDerivedFunctor).obj (((upperStar B
          g).leftDerivedFunctor).obj K)))
        ((derivedTensor B c.Z).flip.obj (((upperStar B c.g).leftDerivedFunctor).obj
          (((upperStar B g).leftDerivedFunctor).obj K)))
        ((derivedTensor B Y).flip.obj (((upperStar B g).leftDerivedFunctor).obj K))
        ((derivedTensor B e.Z).flip.obj (((upperStar B e.g).leftDerivedFunctor).obj (((upperStar B
          d.g).leftDerivedFunctor).obj K)))
        ((derivedTensor B d.Z).flip.obj (((upperStar B d.g).leftDerivedFunctor).obj K))
        ((derivedTensor B Z).flip.obj K)
        (openStrength B c.i (((upperStar B c.g).leftDerivedFunctor).obj (((upperStar B
          g).leftDerivedFunctor).obj K)) ((leftDerivedUpperStarCompactificationIso B c).hom.app
          (((upperStar B g).leftDerivedFunctor).obj K)))
        (properStrength B c.g (((upperStar B g).leftDerivedFunctor).obj K))
        (openStrength B d.i (((upperStar B d.g).leftDerivedFunctor).obj K)
          ((leftDerivedUpperStarCompactificationIso B d).hom.app K))
        (properStrength B d.g K)
        (openStrength B b (((upperStar B e.g).leftDerivedFunctor).obj (((upperStar B
          d.g).leftDerivedFunctor).obj K)) (((derivedSquareUpperStarIso B sq.toCommSq).hom.app
          (((upperStar B d.g).leftDerivedFunctor).obj K)) ≫ ((upperStar B
          c.g).leftDerivedFunctor).map ((leftDerivedUpperStarCompactificationIso B d).hom.app
          K)))
        (properStrength B e.g (((upperStar B d.g).leftDerivedFunctor).obj K))
        (properTwistedStrength B (e.g ≫ d.g) K ((leftDerivedUpperStarComp B e.g d.g (e.g ≫ d.g)
          rfl).hom.app K))
        (openStrength B e.i (((upperStar B e.g).leftDerivedFunctor).obj (((upperStar B
          d.g).leftDerivedFunctor).obj K)) ((leftDerivedUpperStarComp B c.i b e.i
          hoc.symm).hom.app (((upperStar B e.g).leftDerivedFunctor).obj (((upperStar B
          d.g).leftDerivedFunctor).obj K)) ≫ ((upperStar B c.i).leftDerivedFunctor).map
          (((derivedSquareUpperStarIso B sq.toCommSq).hom.app (((upperStar B
          d.g).leftDerivedFunctor).obj K)) ≫ ((upperStar B c.g).leftDerivedFunctor).map
          ((leftDerivedUpperStarCompactificationIso B d).hom.app K)) ≫
          ((leftDerivedUpperStarCompactificationIso B c).hom.app (((upperStar B
          g).leftDerivedFunctor).obj K))))
        (openImmersionLowerShriekLowerStarExchange B sq)
        ((rightDerivedLowerStarComp B e.g d.g).hom)
        ((mapDerivedCategoryOpenImmersionLowerShriekComp B c.i b).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom
        hm
        hp
        ho
        M
        _
        hstrength
      simpa only [openStrength_app, properStrength_app, properTwistedStrength_app,
        projectionMapOfCompactification_app_app, Compactification.comp_Z,
        Compactification.comp_i, Compactification.comp_g, flipFunctor_map_app_app,
        Functor.flip_obj_obj, Functor.flip_obj_map, Functor.flip_map_app,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_obj,
        Functor.comp_map, Functor.map_comp, Category.assoc] using hfinal

omit [HasSmallSiteSheafify B] in
private theorem projectionMapOfCompactification_explicit
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    ((projectionMapOfCompactification B c).app M).app K =
      ((rightDerivedLowerStarProjectionMap B c.g).app
        ((openImmersionLowerShriek B c.i).mapDerivedCategory.obj M)).app K ≫
      (lowerStar B c.g).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app M).app
          ((upperStar B c.g).leftDerivedFunctor.obj K)) ≫
      (rightDerivedLowerShriekOfCompactification B c).map
        (((derivedTensor B X).obj M).map
          ((leftDerivedUpperStarComp B c.i c.g f c.comm).inv.app K)) := by
  have h := projectionMapOfCompactification_app_app B c M K
  have ht := map_iso_app_congr
    ((derivedTensor B X).obj M ⋙ rightDerivedLowerShriekOfCompactification B c)
    (leftDerivedUpperStarCompactificationIso_eq B c) K
  exact h.trans (two_prefix_congr (C := DerivedCategory (Sheaf Y.smallEtaleTopology B)) ht)

omit [HasSmallSiteSheafify B] in
private theorem projectionMapOfCompactification_withData
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (U : Scheme.{u}) (hU : c.Z = U)
    (j : X ⟶ U) [IsOpenImmersion j] (p : U ⟶ Y)
    (hj : c.i ≫ eqToHom hU = j) (hp : eqToHom hU.symm ≫ c.g = p) (hcomp : f = j ≫ p)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    HEq (((projectionMapOfCompactification B c).app M).app K)
      (((rightDerivedLowerStarProjectionMap B p).app
        ((openImmersionLowerShriek B j).mapDerivedCategory.obj M)).app K ≫
      (lowerStar B p).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app M).app
          ((upperStar B p).leftDerivedFunctor.obj K)) ≫
      ((openImmersionLowerShriek B j).mapDerivedCategory ⋙
        (lowerStar B p).rightDerivedFunctor).map
        (((derivedTensor B X).obj M).map
          ((leftDerivedUpperStarComp B j p f hcomp).inv.app K))) := by
  -- Transport the scheme before specializing either derived functor.
  subst U
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hj hp
  subst j p
  exact heq_of_eq (projectionMapOfCompactification_explicit B c M K)

omit [HasSmallSiteSheafify B] in
private theorem towerProjection_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (hcomp : f ≫ g = e.i ≫ (e.g ≫ d.g))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology B)) :
    ((projectionMapOfCompactification B (d.comp e)).app M).app K =
      ((rightDerivedLowerStarProjectionMap B (e.g ≫ d.g)).app
        ((openImmersionLowerShriek B e.i).mapDerivedCategory.obj M)).app K ≫
      (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso B e.i).inv.app M).app
          ((upperStar B (e.g ≫ d.g)).leftDerivedFunctor.obj K)) ≫
      ((openImmersionLowerShriek B e.i).mapDerivedCategory ⋙
        (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor).map
        (((derivedTensor B X).obj M).map
          ((leftDerivedUpperStarComp B e.i (e.g ≫ d.g)
            (f ≫ g) hcomp).inv.app K)) := by
  exact eq_of_heq (projectionMapOfCompactification_withData B (d.comp e) e.Z
    (Compactification.comp_Z d e) e.i (e.g ≫ d.g)
    (by simpa only [eqToHom_refl, Category.comp_id] using Compactification.comp_i d e)
    (by simpa only [eqToHom_refl, Category.id_comp] using Compactification.comp_g d e)
    hcomp M K)

private theorem tower_projection_canonical
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (c : Compactification f) (b : c.Z ⟶ e.Z) [hb : IsOpenImmersion b]
    (sq : IsPullback c.g b d.i e.g) (hoc : c.i ≫ b = e.i)
    (hcomp : f ≫ g = e.i ≫ (e.g ≫ d.g))
    (E : rightDerivedLowerShriekOfCompactification B c ⋙
      rightDerivedLowerShriekOfCompactification B d ≅
      rightDerivedLowerShriekOfCompactification B (d.comp e))
    (hE : ∀ N : DerivedCategory (Sheaf X.smallEtaleTopology B),
      E.hom.app N =
        (lowerStar B d.g).rightDerivedFunctor.map
          ((openImmersionLowerShriekLowerStarExchange B sq).app
            ((openImmersionLowerShriek B c.i).mapDerivedCategory.obj N)) ≫
        (rightDerivedLowerStarComp B e.g d.g).hom.app
          ((openImmersionLowerShriek B b).mapDerivedCategory.obj
            ((openImmersionLowerShriek B c.i).mapDerivedCategory.obj N)) ≫
        (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor.map
          (((mapDerivedCategoryOpenImmersionLowerShriekComp B c.i b).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr B hoc).hom.app N))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology B)) :
    ((projectionMapOfCompactification B d).app
      ((rightDerivedLowerShriekOfCompactification B c).obj M)).app K ≫
        (rightDerivedLowerShriekOfCompactification B d).map
          (((projectionMapOfCompactification B c).app M).app
            ((upperStar B g).leftDerivedFunctor.obj K)) ≫
        E.hom.app (((derivedTensor B X).obj M).obj
          ((upperStar B f).leftDerivedFunctor.obj
            ((upperStar B g).leftDerivedFunctor.obj K))) =
      ((derivedTensor B Z).map (E.hom.app M)).app K ≫
        ((projectionMapOfCompactification B (d.comp e)).app M).app K ≫
        (rightDerivedLowerShriekOfCompactification B (d.comp e)).map
          (((derivedTensor B X).obj M).map
            ((leftDerivedUpperStarComp B f g (f ≫ g) rfl).hom.app K)) := by
  have h := tower_projection B f g d e c b sq hoc hcomp M K
  have he := hE (((derivedTensor B X).obj M).obj
    ((upperStar B f).leftDerivedFunctor.obj
      ((upperStar B g).leftDerivedFunctor.obj K)))
  have ht := tensor_map_congr (derivedTensor B Z) (hE M) K
  have hp := morphism_comp_congr (C := DerivedCategory (Sheaf Z.smallEtaleTopology B))
    (towerProjection_app B f g d e hcomp M K)
    (towerModel_map B f g d e (((derivedTensor B X).obj M).map
      ((leftDerivedUpperStarComp B f g (f ≫ g) rfl).hom.app K)))
  have result := chain_endpoint_transport
    (C := DerivedCategory (Sheaf Z.smallEtaleTopology B)) he ht hp h
  exact result

end Generic

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

local instance essentiallySmall_etale_shriekTensor (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
attribute [local implicit_reducible] Compactification.restrict Compactification.ofIsPullback
  Compactification.comp Compactification.copy Compactification.postcomp
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor projectionMapOfCompactification
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  openImmersionLowerShriek upperStar lowerStar

attribute [local implicit_reducible] derivedTensorRightDerivedLowerStar
  rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] derivedOpenImmersionLowerShriekProjectionIso
  rightDerivedLowerStarComp rightDerivedLowerStarProjectionMap
  openImmersionLowerShriekLowerStarExchange mapDerivedCategoryOpenImmersionLowerShriekComp
  mapDerivedCategoryOpenImmersionLowerShriekCongr leftDerivedUpperStarComp
  derivedSquareUpperStarIso leftDerivedUpperStarCompactificationIso

private theorem towerCompositor_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (N : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app N =
      (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor.map
        ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A)
          (towerSquare d e)).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory.obj
              N)) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g d.g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) (towerOpen d e)).mapDerivedCategory.obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategory.obj N))
            ≫
      (lowerStar (ModuleCat.{u + 1} A) (e.g ≫ d.g)).rightDerivedFunctor.map
        (((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A)
            e.restrict.i (towerOpen d e)).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A)
            (towerOpen_comp d e)).hom.app N) := by
  simp only [towerOpen, rightDerivedLowerShriekOfCompactificationCompIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, asIso_hom, Functor.comp_obj, Category.id_comp, Category.assoc]

attribute [local irreducible] rightDerivedLowerShriekOfCompactificationCompIso

theorem projectionMapOfCompactification_tower_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) d).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict).obj M)).app K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          (((projectionMapOfCompactification (ModuleCat.{u + 1} A) e.restrict).app M).app
          (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)) ≫
        (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app (((derivedTensor
          (ModuleCat.{u + 1} A) X).obj M).obj (((upperStar (ModuleCat.{u + 1} A)
          f).leftDerivedFunctor).obj (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj
          K))) =
      ((derivedTensor (ModuleCat.{u + 1} A) Z).map
        ((rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app M)).app K ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A) (d.comp e)).app M).app K ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e)).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map ((leftDerivedUpperStarComp
          (ModuleCat.{u + 1} A) f g (f ≫ g) rfl).hom.app K)) := by
  have hcomp : f ≫ g = e.i ≫ (e.g ≫ d.g) := by
    calc
      _ = f ≫ (d.i ≫ d.g) := congrArg (f ≫ ·) d.comm
      _ = (f ≫ d.i) ≫ d.g := (Category.assoc f d.i d.g).symm
      _ = (e.i ≫ e.g) ≫ d.g := congrArg (· ≫ d.g) e.comm
      _ = _ := Category.assoc e.i e.g d.g
  exact tower_projection_canonical (hb := towerOpen_isOpen d e) (ModuleCat.{u + 1} A)
    f g d e e.restrict (towerOpen d e) (towerSquare d e) (towerOpen_comp d e) hcomp
    (rightDerivedLowerShriekOfCompactificationCompIso A d e)
    (towerCompositor_app A f g d e) M K

end AlgebraicGeometry.Etale
