/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import all WeilConjectures.AlgebraicGeometry.SfExactExchangePasting

/-! # Intersection pasting under a proper ambient change

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D, proper-projection grid.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private def graphTriangle
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasBaseChange]
    {X I O : Scheme.{u}} (s : X ⟶ I) (v : I ⟶ O) (a : X ⟶ O)
    [IsOpenImmersion v] (h : s ≫ v = a) : F.pf s ⋙ F.sh v ⟶ F.pf a :=
  let sq : IsPullback s (𝟙 X) v a :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using h⟩
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
  (F.exchange s (𝟙 X) v a sq.w) ≫
    Functor.whiskerRight (F.shId X).hom (F.pf a) ≫ (Functor.leftUnitor _).hom

private theorem graphTriangle_proper_square
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasBaseChange]
    {X I I' O O' : Scheme.{u}}
    (s : X ⟶ I) (s' : X ⟶ I') (a : X ⟶ O) (a' : X ⟶ O')
    (v : I ⟶ O) (v' : I' ⟶ O') [IsOpenImmersion v] [IsOpenImmersion v']
    (q : I' ⟶ I) (r : O' ⟶ O) (sq : IsPullback q v' v r)
    (hs : s' ≫ q = s) (ha : a' ≫ r = a)
    (hv : s ≫ v = a) (hv' : s' ≫ v' = a') (M : F.obj X) :
    let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
    (graphTriangle F s v a hv).app M ≫ (F.pfComp' a' r a ha).hom.app M =
      (F.sh v).map ((F.pfComp' s' q s hs).hom.app M) ≫
        (F.exchange q v' v r sq.w).app ((F.pf s').obj M) ≫
        (F.pf r).map ((graphTriangle F s' v' a' hv').app M) := by
  let st : IsPullback s (𝟙 X) v a :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hv⟩
  let st' : IsPullback s' (𝟙 X) v' a' :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hv'⟩
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) st
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) st'
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sq
  have hp := congr_app (F.exchange_paste_horiz s' q (𝟙 X) v' v a' r s a
    st'.w sq.w hs ha st.w) M
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id] at hp
  have hn := (F.pfComp' a' r a ha).hom.naturality ((F.shId X).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  simp only [graphTriangle, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.assoc, Category.comp_id]
  rw [hn, ← Category.assoc, hp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]

private theorem graphTriangle_open_square
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasBaseChange]
    {X I I' O O' T T' : Scheme.{u}}
    (s : X ⟶ I) (s' : X ⟶ I') (a : X ⟶ O) (a' : X ⟶ O')
    (v : I ⟶ O) (v' : I' ⟶ O') (b : O ⟶ T) (b' : O' ⟶ T')
    (e : I ⟶ T) (e' : I' ⟶ T')
    [IsOpenImmersion v] [IsOpenImmersion v']
    [IsOpenImmersion b] [IsOpenImmersion b']
    [IsOpenImmersion e] [IsOpenImmersion e']
    (q : I' ⟶ I) (r : O' ⟶ O) (R : T' ⟶ T)
    (sqv : IsPullback q v' v r) (sqb : IsPullback r b' b R)
    (sqe : IsPullback q e' e R) (he : v ≫ b = e) (he' : v' ≫ b' = e')
    (hs : s' ≫ q = s) (ha : a' ≫ r = a)
    (hv : s ≫ v = a) (hv' : s' ≫ v' = a') (M : F.obj X) :
    let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sqb
    let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
      sqe
    (F.shComp' v b e he).hom.app ((F.pf s).obj M) ≫
        (F.sh b).map ((graphTriangle F s v a hv).app M) ≫
        (F.sh b).map ((F.pfComp' a' r a ha).hom.app M) ≫
        (F.exchange r b' b R sqb.w).app ((F.pf a').obj M) =
      (F.sh e).map ((F.pfComp' s' q s hs).hom.app M) ≫
        (F.exchange q e' e R sqe.w).app
          ((F.pf s').obj M) ≫
        (F.pf R).map
          ((F.shComp' v' b' e' he').hom.app ((F.pf s').obj M) ≫
            (F.sh b').map ((graphTriangle F s' v' a' hv').app M)) := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sqv
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) sqb
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F)
    sqe
  have ht := graphTriangle_proper_square F s s' a a' v v' q r sqv hs ha hv hv' M
  have hp := congr_app (F.exchange_paste_vert q r R v' v b' b
    e' e sqv.w sqb.w he' he sqe.w)
      ((F.pf s').obj M)
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id] at hp
  have hp' := congrArg
    (fun z ↦ z ≫ (F.pf R).map
      ((F.shComp' v' b' e' he').hom.app ((F.pf s').obj M))) hp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.map_id, Category.comp_id] at hp'
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id] at hp'
  have hn := (F.exchange r b' b R sqb.w).naturality
    ((graphTriangle F s' v' a' hv').app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have hc := (F.shComp' v b e he).hom.naturality
    ((F.pfComp' s' q s hs).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hc
  dsimp only at ht ⊢
  rw [← (F.sh b).map_comp_assoc, ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  rw [← reassoc_of% hc]
  rw [reassoc_of% hp'.symm]

attribute [local instance] unbounded_has_base_change

private theorem graph_identity_leftAdjoint_compare
    {C : Type*} [Category C] {F G : C ⥤ C} (adj : F ⊣ G) (e : G ≅ 𝟭 C) :
    adj.leftAdjointUniq (Adjunction.id.ofNatIsoRight e.symm) =
      Adjunction.leftAdjointIdIso adj e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (adj.homEquiv X X).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp [Adjunction.leftAdjointIdIso, conjugateIsoEquiv,
    Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit]

private theorem graph_open_id_conjugate
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
        ).mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom =
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).inv := by
  let B := ModuleCat.{u + 1} A
  let a := openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let e := Adjunction.leftAdjointIdIso a (upperStarId B X)
  have hu (K : Sheaf X.smallEtaleTopology B) :
      a.unit.app K ≫ (upperStar B (𝟙 X)).map (e.hom.app K) =
        Adjunction.id.unit.app K ≫ (upperStarId B X).inv.app K := by
    have h := unit_conjugateEquiv Adjunction.id a e.hom K
    simpa only [Adjunction.conjugateEquiv_leftAdjointIdIso_hom, e,
      Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj, Category.id_comp]
      using h.symm
  have hd := exact_adj_conjugate
    (C := Sheaf X.smallEtaleTopology B) (D := Sheaf X.smallEtaleTopology B)
    a Adjunction.id e (upperStarId B X).symm hu
  rw [exact_adj_id (C := Sheaf X.smallEtaleTopology B)] at hd
  apply identity_conjugate_of_unit
  simpa only [Functor.mapDerivedCategoryNatIso_symm] using hd

private theorem graph_sh_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (unboundedFormalism A).shId X =
      mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X := by
  rw [mapDerivedCategoryOpenImmersionLowerShriekId, openImmersionLowerShriekId,
    graph_identity_leftAdjoint_compare, ExchangeFormalism.shId]
  apply conjugate_iso_symm_eq
  exact graph_open_id_conjugate A X

private theorem graph_open_exchange
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := unboundedFormalism A) sq
    ((unboundedFormalism A).exchange t l r b sq.w) =
      openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) sq
  dsimp only [ExchangeFormalism.exchange, openImmersionLowerShriekLowerStarExchange]
  have hh : inv ((unboundedFormalism A).baseChange t l r b sq.w) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change A sq]
    exact Iso.hom_inv_id _
  rw [hh]
  rfl

private theorem graphTriangle_concrete
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I O : Scheme.{u}} (s : X ⟶ I) (v : I ⟶ O) (a : X ⟶ O)
    [IsOpenImmersion v] [IsProper a] (h : s ≫ v = a) :
    graphTriangle (unboundedFormalism A) s v a h =
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s v a h).hom := by
  let sq : IsPullback s (𝟙 X) v a :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using h⟩
  have hid := graph_sh_id A X
  simp only [graphTriangle, graph_open_exchange A sq, hid,
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom]
  rfl

private theorem graph_pf_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    (unboundedFormalism A).pfComp' f g h w =
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g h w).symm := by
  subst h
  exact unbounded_pf_comp A f g

private theorem graphTriangle_open_square_concrete
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I I' O O' T T' : Scheme.{u}}
    (s : X ⟶ I) (s' : X ⟶ I') (a : X ⟶ O) (a' : X ⟶ O')
    (v : I ⟶ O) (v' : I' ⟶ O') (b : O ⟶ T) (b' : O' ⟶ T')
    (e : I ⟶ T) (e' : I' ⟶ T')
    [IsOpenImmersion v] [IsOpenImmersion v']
    [IsOpenImmersion b] [IsOpenImmersion b']
    [IsOpenImmersion e] [IsOpenImmersion e'] [IsProper a] [IsProper a']
    (q : I' ⟶ I) (r : O' ⟶ O) (R : T' ⟶ T) [IsProper r] [IsProper R]
    (sqv : IsPullback q v' v r) (sqb : IsPullback r b' b R)
    (sqe : IsPullback q e' e R) (he : v ≫ b = e) (he' : v' ≫ b' = e')
    (hs : s' ≫ q = s) (ha : a' ≫ r = a)
    (hv : s ≫ v = a) (hv' : s' ≫ v' = a') (M : DerivedCategoryModule A X) :
    ((mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) he.symm) ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) v b).hom.app (R((s)_*[ModuleCat.{u + 1} A]).obj M) ≫
      D((b)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s v a hv).hom.app M) ≫
      D((b)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) a' r a ha).inv.app M) ≫
      (openImmersionLowerShriekLowerStarExchangeIso A sqb).hom.app
        (R((a')_*[ModuleCat.{u + 1} A]).obj M) =
    D((e)_!open[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) s' q s hs).inv.app M) ≫
      (openImmersionLowerShriekLowerStarExchangeIso A sqe).hom.app
        (R((s')_*[ModuleCat.{u + 1} A]).obj M) ≫
      R((R)_*[ModuleCat.{u + 1} A]).map
        (((mapDerivedCategoryOpenImmersionLowerShriekCongr
            (ModuleCat.{u + 1} A) he'.symm) ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) v' b').hom.app
            (R((s')_*[ModuleCat.{u + 1} A]).obj M) ≫
          D((b')_!open[ModuleCat.{u + 1} A]).map
            ((rightDerivedLowerStarCompOpenImmersionLowerShriekIso
              A s' v' a' hv').hom.app M)) := by
  have h := graphTriangle_open_square (unboundedFormalism A) s s' a a' v v' b b' e e'
    q r R sqv sqb sqe he he' hs ha hv hv' M
  simp only [graphTriangle_concrete, graph_pf_comp, Iso.symm_hom,
    unbounded_sh_comp,
    graph_open_exchange A sqb, graph_open_exchange A sqe] at h
  simpa only [unboundedFormalism, openImmersionLowerShriekLowerStarExchangeIso,
    asIso_hom] using h

private theorem graph_open_congr_refl
    (A : Type (u + 1)) [CommRing A]
    {I T : Scheme.{u}} (e : I ⟶ T) [IsOpenImmersion e] :
    mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} A) (rfl : e = e) = Iso.refl _ := rfl

private def ambientLeg
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I O T : Scheme.{u}} (s : X ⟶ I) (v : I ⟶ O) (b : O ⟶ T) (a : X ⟶ O)
    (e : I ⟶ T) [IsOpenImmersion e]
    [IsOpenImmersion v] [IsOpenImmersion b] [IsProper a]
    (he : v ≫ b = e) (h : s ≫ v = a) :
    R((s)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ≅
      R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((b)_!open[ModuleCat.{u + 1} A]) :=
  Functor.isoWhiskerLeft _
      ((mapDerivedCategoryOpenImmersionLowerShriekCongr
          (ModuleCat.{u + 1} A) he.symm) ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) v b) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A s v a h) _

private def ambientLegOver
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I O T Y : Scheme.{u}} (s : X ⟶ I) (v : I ⟶ O) (b : O ⟶ T) (a : X ⟶ O)
    (e : I ⟶ T) [IsOpenImmersion e]
    [IsOpenImmersion v] [IsOpenImmersion b] [IsProper a]
    (he : v ≫ b = e) (h : s ≫ v = a)
    (p : T ⟶ Y) :
    R((s)_*[ModuleCat.{u + 1} A]) ⋙ D((e)_!open[ModuleCat.{u + 1} A]) ⋙
        R((p)_*[ModuleCat.{u + 1} A]) ≅
      R((a)_*[ModuleCat.{u + 1} A]) ⋙ D((b)_!open[ModuleCat.{u + 1} A]) ⋙
        R((p)_*[ModuleCat.{u + 1} A]) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ambientLeg A s v b a e he h) _ ≪≫
    Functor.associator _ _ _

private theorem ambientLegOver_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X I I' O O' T T' Y : Scheme.{u}}
    (s : X ⟶ I) (s' : X ⟶ I') (a : X ⟶ O) (a' : X ⟶ O')
    (v : I ⟶ O) (v' : I' ⟶ O') (b : O ⟶ T) (b' : O' ⟶ T')
    (e : I ⟶ T) (e' : I' ⟶ T')
    [IsOpenImmersion v] [IsOpenImmersion v']
    [IsOpenImmersion b] [IsOpenImmersion b']
    [IsOpenImmersion e] [IsOpenImmersion e'] [IsProper a] [IsProper a']
    (q : I' ⟶ I) (r : O' ⟶ O) (R : T' ⟶ T) [IsProper r] [IsProper R]
    (sqv : IsPullback q v' v r) (sqb : IsPullback r b' b R)
    (sqe : IsPullback q e' e R) (he : v ≫ b = e) (he' : v' ≫ b' = e')
    (hs : s' ≫ q = s) (ha : a' ≫ r = a)
    (hv : s ≫ v = a) (hv' : s' ≫ v' = a')
    (p : T ⟶ Y) (p' : T' ⟶ Y) (hp : R ≫ p = p') :
    (ambientLegOver A s v b a e he hv p).hom ≫
        (etaleProperAmbientTransport A a b p a' b' p' R r sqb ha hp).hom =
      (etaleProperAmbientTransport A s e p s' e' p' R q
        sqe hs hp).hom ≫
        (ambientLegOver A s' v' b' a' e' he' hv' p').hom := by
  apply NatTrans.ext
  funext M
  have h := graphTriangle_open_square_concrete A s s' a a' v v' b b' e e'
    q r R sqv sqb sqe he he' hs ha hv hv' M
  let K := (ambientLeg A s' v' b' a' e' he' hv').hom.app M
  have hn := (rightDerivedLowerStarCompOfEq
    (ModuleCat.{u + 1} A) R p p' hp).hom.naturality K
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have hh := congrArg
    (fun z ↦ R((p)_*[ModuleCat.{u + 1} A]).map z ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) R p p' hp).hom.app
        ((R((a')_*[ModuleCat.{u + 1} A]) ⋙
          D((b')_!open[ModuleCat.{u + 1} A])).obj M)) h
  simp only [ambientLegOver, ambientLeg, etaleProperAmbientTransport,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    CategoryTheory.Functor.map_id, Functor.map_comp, Category.assoc] at hh ⊢
  have hn' :
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) R p p' hp).hom.app
          ((R((s')_*[ModuleCat.{u + 1} A]) ⋙
            D((e')_!open[ModuleCat.{u + 1} A])).obj M) ≫
        R((p')_*[ModuleCat.{u + 1} A]).map K =
      R((p)_*[ModuleCat.{u + 1} A]).map
          (R((R)_*[ModuleCat.{u + 1} A]).map K) ≫
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) R p p' hp).hom.app
          ((R((a')_*[ModuleCat.{u + 1} A]) ⋙
            D((b')_!open[ModuleCat.{u + 1} A])).obj M) := hn.symm
  dsimp only [K, ambientLeg] at hn'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.id_obj, CategoryTheory.Functor.map_id,
    Category.comp_id, Functor.map_comp, Category.assoc] at hn'
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at hn'
  rw [hn']
  exact hh

private def intersectionMap
    {O₁ O₂ T O₁' O₂' T' : Scheme.{u}}
    (b₁ : O₁ ⟶ T) (b₂ : O₂ ⟶ T) (b₁' : O₁' ⟶ T') (b₂' : O₂' ⟶ T')
    (r₁ : O₁' ⟶ O₁) (r₂ : O₂' ⟶ O₂) (R : T' ⟶ T)
    (sq₁ : IsPullback r₁ b₁' b₁ R) (sq₂ : IsPullback r₂ b₂' b₂ R) :
    pullback b₁' b₂' ⟶ pullback b₁ b₂ :=
  pullback.lift (pullback.fst _ _ ≫ r₁) (pullback.snd _ _ ≫ r₂) (by
    rw [Category.assoc, sq₁.w, ← Category.assoc, pullback.condition,
      Category.assoc, ← sq₂.w, ← Category.assoc])

private theorem intersectionMap_fst_isPullback
    {O₁ O₂ T O₁' O₂' T' : Scheme.{u}}
    (b₁ : O₁ ⟶ T) (b₂ : O₂ ⟶ T) (b₁' : O₁' ⟶ T') (b₂' : O₂' ⟶ T')
    (r₁ : O₁' ⟶ O₁) (r₂ : O₂' ⟶ O₂) (R : T' ⟶ T)
    (sq₁ : IsPullback r₁ b₁' b₁ R) (sq₂ : IsPullback r₂ b₂' b₂ R) :
    IsPullback (intersectionMap b₁ b₂ b₁' b₂' r₁ r₂ R sq₁ sq₂)
      (pullback.fst b₁' b₂') (pullback.fst b₁ b₂) r₁ := by
  apply IsPullback.of_right (h₁₂ := pullback.snd b₁ b₂)
    (h₂₂ := b₁) (v₁₃ := b₂)
  · simpa only [intersectionMap, pullback.lift_snd, sq₁.w] using
      ((IsPullback.of_hasPullback b₁' b₂').flip.paste_horiz sq₂)
  · simp only [intersectionMap, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback b₁ b₂).flip

private theorem intersectionMap_snd_isPullback
    {O₁ O₂ T O₁' O₂' T' : Scheme.{u}}
    (b₁ : O₁ ⟶ T) (b₂ : O₂ ⟶ T) (b₁' : O₁' ⟶ T') (b₂' : O₂' ⟶ T')
    (r₁ : O₁' ⟶ O₁) (r₂ : O₂' ⟶ O₂) (R : T' ⟶ T)
    (sq₁ : IsPullback r₁ b₁' b₁ R) (sq₂ : IsPullback r₂ b₂' b₂ R) :
    IsPullback (intersectionMap b₁ b₂ b₁' b₂' r₁ r₂ R sq₁ sq₂)
      (pullback.snd b₁' b₂') (pullback.snd b₁ b₂) r₂ := by
  apply IsPullback.of_right (h₁₂ := pullback.fst b₁ b₂)
    (h₂₂ := b₂) (v₁₃ := b₁)
  · simpa only [intersectionMap, pullback.lift_fst, sq₂.w] using
      ((IsPullback.of_hasPullback b₁' b₂').paste_horiz sq₁)
  · simp only [intersectionMap, pullback.lift_snd]
  · exact IsPullback.of_hasPullback b₁ b₂

private theorem cancel_intersection_transport
    {C : Type*} [Category C] {I I' O₁ O₂ O₁' O₂' : C}
    (L₁ : I ≅ O₁) (L₂ : I ≅ O₂) (L₁' : I' ≅ O₁') (L₂' : I' ≅ O₂')
    (D : I ≅ I') (D₁ : O₁ ≅ O₁') (D₂ : O₂ ≅ O₂')
    (h₁ : L₁.hom ≫ D₁.hom = D.hom ≫ L₁'.hom)
    (h₂ : L₂.hom ≫ D₂.hom = D.hom ≫ L₂'.hom) :
    (L₁.symm ≪≫ L₂).hom ≫ D₂.hom =
      D₁.hom ≫ (L₁'.symm ≪≫ L₂').hom := by
  apply (cancel_epi L₁.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]
  rw [h₂, h₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The intersection graph comparison is natural for a proper ambient map.

Source: Stacks Project, more-etale.tex, Tags 0F7C and 0F7D, vertical and horizontal
pasting in the proper-projection grid.
(auxiliary; not a blueprint node).

Proof: form the map from the new intersection to the old one by the universal
property of the two neighborhood squares. The map and its two projections are
Cartesian over the corresponding proper product map, and the graph lifts commute
with them. The two identity-top graph triangles used in the middle comparison
are therefore compatible with the two proper neighborhood squares. Apply horizontal
pasting to each graph triangle beside its projection square, then vertical pasting
to each pair of open inclusions from the intersection to the product. Naturality
interchanges the two exchanges meeting at a vertex. After expanding the two middle
words, the exchanges for the map on intersections occur with opposite orientations
and cancel. Associativity of the open compositors identifies the common composite
open inclusion; associativity of the proper compositors identifies the two maps to Y.
Whiskering the remaining equation by the proper direct image to Y and inserting the
two functor associators yields the equation below. Neither side comparison nor the
final graph comparison is used. No quasi-compactness is needed; the same identities
apply if a neighborhood is empty or the proper ambient map is an identity. -/
theorem etaleGraphProperAmbientMiddle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) (pr : t.P ⟶ s.P) [IsProper pr]
    (q : t.U ⟶ s.U) (sq : IsPullback q t.e s.e pr)
    (hz : t.a ≫ q = s.a) (hp : pr ≫ s.p = t.p)
    [IsProper (locallyClosedGraphS₁ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)))]
    [IsProper (locallyClosedGraphS₂ s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)))]
    [IsProper (locallyClosedGraphS₁ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm)))]
    [IsProper (locallyClosedGraphS₂ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm)))] :
    let M_s := (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (locallyClosedGraphMiddle s.a s.e s.p c.i c.g
      ((Category.assoc _ _ _).trans (s.fac.trans c.comm)) A)
        R((pullback.fst s.p c.g ≫ s.p)_*[ModuleCat.{u + 1} A]) ≪≫
      Functor.associator _ _ _
    let M_t := (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (locallyClosedGraphMiddle t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) A)
        R((pullback.fst t.p c.g ≫ t.p)_*[ModuleCat.{u + 1} A]) ≪≫
      Functor.associator _ _ _
    M_s.hom ≫ (s.properAmbientSecondTransport c t pr q sq hz hp A).hom =
      (s.properAmbientFirstTransport c t pr q sq hz hp A).hom ≫ M_t.hom := by
  let h (H : EtaleGraphPresentation f) :=
    (Category.assoc H.a H.e H.p).trans (H.fac.trans c.comm)
  let s₁ (H : EtaleGraphPresentation f) :=
    locallyClosedGraphS₁ H.a H.e H.p c.i c.g (h H)
  let s₂ (H : EtaleGraphPresentation f) :=
    locallyClosedGraphS₂ H.a H.e H.p c.i c.g (h H)
  let (H : EtaleGraphPresentation f) : IsProper (s₁ H) :=
    (Classical.choice
      (etaleLocallyClosedGraphModel A H.a H.e H.p c.i c.g c.comm.symm H.fac)).properS₁
  let (H : EtaleGraphPresentation f) : IsProper (s₂ H) :=
    (Classical.choice
      (etaleLocallyClosedGraphModel A H.a H.e H.p c.i c.g c.comm.symm H.fac)).properS₂
  let S (H : EtaleGraphPresentation f) :=
    locallyClosedGraphS₁₂ H.a H.e H.p c.i c.g (h H)
  let b₁ (H : EtaleGraphPresentation f) := pullback.fst (pullback.snd H.p c.g) c.i
  let b₂ (H : EtaleGraphPresentation f) := pullback.fst (pullback.fst H.p c.g) H.e
  let u₁ (H : EtaleGraphPresentation f) := pullback.fst (b₁ H) (b₂ H)
  let u₂ (H : EtaleGraphPresentation f) := pullback.snd (b₁ H) (b₂ H)
  let e (H : EtaleGraphPresentation f) := u₁ H ≫ b₁ H
  let p (H : EtaleGraphPresentation f) := pullback.fst H.p c.g ≫ H.p
  have hv₁ (H : EtaleGraphPresentation f) : S H ≫ u₁ H = s₁ H :=
    pullback.lift_fst _ _ _
  have hv₂ (H : EtaleGraphPresentation f) : S H ≫ u₂ H = s₂ H :=
    pullback.lift_snd _ _ _
  have he₂ (H : EtaleGraphPresentation f) : u₂ H ≫ b₂ H = e H :=
    pullback.condition.symm
  let L₁ (H : EtaleGraphPresentation f) :=
    ambientLegOver A (S H) (u₁ H) (b₁ H) (s₁ H) (e H) rfl (hv₁ H) (p H)
  let L₂ (H : EtaleGraphPresentation f) :=
    ambientLegOver A (S H) (u₂ H) (b₂ H) (s₂ H) (e H) (he₂ H) (hv₂ H) (p H)
  have hm (H : EtaleGraphPresentation f) :
      (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (locallyClosedGraphMiddle H.a H.e H.p c.i c.g (h H) A)
            R((p H)_*[ModuleCat.{u + 1} A]) ≪≫
          Functor.associator _ _ _ = (L₁ H).symm ≪≫ L₂ H := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [L₁, L₂, ambientLegOver, ambientLeg, s₁, s₂, S, b₁, b₂, u₁, u₂, e, p, h,
      locallyClosedGraphMiddle,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Functor.id_obj, Functor.map_comp,
      graph_open_congr_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.assoc, Category.id_comp, Category.comp_id]
  let R := s.properAmbientProduct c t pr hp
  let r₁ := s.properAmbientFirst c t pr hp
  let r₂ := s.properAmbientSecond c t pr q sq hp
  let sq₁ := s.properAmbientFirst_isPullback c t pr hp
  let sq₂ := s.properAmbientSecond_isPullback c t pr q sq hp
  let Q := intersectionMap (b₁ s) (b₂ s) (b₁ t) (b₂ t) r₁ r₂ R sq₁ sq₂
  have sqv₁ : IsPullback Q (u₁ t) (u₁ s) r₁ :=
    intersectionMap_fst_isPullback _ _ _ _ _ _ _ sq₁ sq₂
  have sqv₂ : IsPullback Q (u₂ t) (u₂ s) r₂ :=
    intersectionMap_snd_isPullback _ _ _ _ _ _ _ sq₁ sq₂
  have sqe : IsPullback Q (e t) (e s) R := sqv₁.paste_vert sq₁
  have hs₁ : s₁ t ≫ r₁ = s₁ s := s.properAmbientFirst_graph c t pr q sq hz hp
  have hs₂ : s₂ t ≫ r₂ = s₂ s := s.properAmbientSecond_graph c t pr q sq hz hp
  have hQ₁ : Q ≫ u₁ s = u₁ t ≫ r₁ := pullback.lift_fst _ _ _
  have hQ₂ : Q ≫ u₂ s = u₂ t ≫ r₂ := pullback.lift_snd _ _ _
  have hS : S t ≫ Q = S s := by
    apply pullback.hom_ext
    · change (S t ≫ Q) ≫ u₁ s = S s ≫ u₁ s
      rw [Category.assoc, hQ₁, ← Category.assoc, hv₁, hv₁]
      exact hs₁
    · change (S t ≫ Q) ≫ u₂ s = S s ≫ u₂ s
      rw [Category.assoc, hQ₂, ← Category.assoc, hv₂, hv₂]
      exact hs₂
  have hpR : R ≫ p s = p t := s.properAmbientProduct_base c t pr hp
  let : IsProper r₁ := MorphismProperty.of_isPullback sq₁.flip inferInstance
  let : IsProper r₂ := MorphismProperty.of_isPullback sq₂.flip inferInstance
  let D := etaleProperAmbientTransport A (S s) (e s) (p s) (S t) (e t) (p t)
    R Q sqe hS hpR
  have hn₁ : (L₁ s).hom ≫ (s.properAmbientFirstTransport c t pr q sq hz hp A).hom =
      D.hom ≫ (L₁ t).hom :=
    ambientLegOver_natural A (S s) (S t) (s₁ s) (s₁ t)
      (u₁ s) (u₁ t) (b₁ s) (b₁ t) (e s) (e t) Q r₁ R sqv₁ sq₁ sqe rfl rfl
      hS hs₁ (hv₁ s) (hv₁ t) (p s) (p t) hpR
  have hn₂ : (L₂ s).hom ≫ (s.properAmbientSecondTransport c t pr q sq hz hp A).hom =
      D.hom ≫ (L₂ t).hom :=
    ambientLegOver_natural A (S s) (S t) (s₂ s) (s₂ t)
      (u₂ s) (u₂ t) (b₂ s) (b₂ t) (e s) (e t) Q r₂ R sqv₂ sq₂ sqe (he₂ s) (he₂ t)
      hS hs₂ (hv₂ s) (hv₂ t) (p s) (p t) hpR
  dsimp only
  rw [hm s, hm t]
  exact cancel_intersection_transport (L₁ s) (L₂ s) (L₁ t) (L₂ t) D
    (s.properAmbientFirstTransport c t pr q sq hz hp A)
    (s.properAmbientSecondTransport c t pr q sq hz hp A) hn₁ hn₂

end AlgebraicGeometry.Etale
