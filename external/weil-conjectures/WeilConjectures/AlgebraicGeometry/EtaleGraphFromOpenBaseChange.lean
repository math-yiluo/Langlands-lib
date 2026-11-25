/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import all WeilConjectures.AlgebraicGeometry.SfExactExchangePasting

/-! # Base change of a single explicit product-graph map

Source: Stacks Project, Tag 0F7F, applied factor by factor to the graph formula.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  rightDerivedLowerStarComp rightDerivedLowerStarIdIso
  mapDerivedCategoryOpenImmersionLowerShriekComp
  mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso exactDerivedBaseChangeMap

/-- A functor word together with its successive base-change exchange. -/
private structure ExchangeWord
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (P : C ⥤ C') (Q : D ⥤ D') where
  top : C ⥤ D
  bot : C' ⥤ D'
  exchange : top ⋙ Q ⟶ P ⋙ bot

private def ExchangeWord.comp
    {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    {P : C ⥤ C'} {Q : D ⥤ D'} {R : E ⥤ E'}
    (w : ExchangeWord P Q) (z : ExchangeWord Q R) : ExchangeWord P R where
  top := w.top ⋙ z.top
  bot := w.bot ⋙ z.bot
  exchange := (TwoSquare.hComp (TwoSquare.mk _ _ _ _ w.exchange)
    (TwoSquare.mk _ _ _ _ z.exchange))

private def ExchangeWord.id
    {C C' : Type*} [Category C] [Category C'] (P : C ⥤ C') : ExchangeWord P P where
  top := 𝟭 C
  bot := 𝟭 C'
  exchange := (Functor.leftUnitor P).hom ≫ (Functor.rightUnitor P).inv

/-- An isomorphism of words which commutes with their exchanges. -/
private structure ExchangeIso
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} (w z : ExchangeWord P Q) where
  top : w.top ≅ z.top
  bot : w.bot ≅ z.bot
  comm : Functor.whiskerRight top.hom Q ≫ z.exchange =
    w.exchange ≫ Functor.whiskerLeft P bot.hom

private def ExchangeIso.trans
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} {w z t : ExchangeWord P Q}
    (e : ExchangeIso w z) (d : ExchangeIso z t) : ExchangeIso w t where
  top := e.top ≪≫ d.top
  bot := e.bot ≪≫ d.bot
  comm := by
    simp only [Iso.trans_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
    rw [Category.assoc, d.comm, ← Category.assoc, e.comm, Category.assoc]

private def ExchangeIso.symm
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} {w z : ExchangeWord P Q}
    (e : ExchangeIso w z) : ExchangeIso z w where
  top := e.top.symm
  bot := e.bot.symm
  comm := by
    ext K
    have h := congr_app e.comm K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h ⊢
    apply (cancel_mono (e.bot.hom.app (P.obj K))).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← h, ← Category.assoc, ← Q.map_comp, Iso.inv_hom_id_app, Q.map_id]
    erw [Category.id_comp, Category.comp_id]

private def ExchangeIso.comp
    {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    {P : C ⥤ C'} {Q : D ⥤ D'} {R : E ⥤ E'}
    {w w' : ExchangeWord P Q} {z z' : ExchangeWord Q R}
    (e : ExchangeIso w w') (d : ExchangeIso z z') :
    ExchangeIso (w.comp z) (w'.comp z') where
  top := Functor.isoWhiskerRight e.top z.top ≪≫ Functor.isoWhiskerLeft w'.top d.top
  bot := Functor.isoWhiskerRight e.bot z.bot ≪≫ Functor.isoWhiskerLeft w'.bot d.bot
  comm := by
    ext K
    have he := congr_app e.comm K
    have hd := congr_app d.comm (w'.top.obj K)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at he hd
    simp only [ExchangeWord.comp, TwoSquare.hComp, TwoSquare.mk,
      Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    have hn := z.exchange.naturality (e.top.hom.app K)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hd, reassoc_of% hn]
    have hn' := d.bot.hom.naturality (w'.exchange.app K)
    dsimp only [Functor.comp_obj] at hn'
    rw [← hn']
    rw [← z.bot.map_comp_assoc, he, Functor.map_comp, Category.assoc]

private def ExchangeIso.refl
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} (w : ExchangeWord P Q) : ExchangeIso w w where
  top := Iso.refl _
  bot := Iso.refl _
  comm := by simp

private def ExchangeIso.associator
    {C C' D D' E E' F F' : Type*}
    [Category C] [Category C'] [Category D] [Category D']
    [Category E] [Category E'] [Category F] [Category F']
    {P : C ⥤ C'} {Q : D ⥤ D'} {R : E ⥤ E'} {S : F ⥤ F'}
    (w : ExchangeWord P Q) (z : ExchangeWord Q R) (t : ExchangeWord R S) :
    ExchangeIso ((w.comp z).comp t) (w.comp (z.comp t)) where
  top := Functor.associator _ _ _
  bot := Functor.associator _ _ _
  comm := by
    ext K
    simp [ExchangeWord.comp, TwoSquare.hComp, Functor.map_comp, Category.assoc]

private def ExchangeIso.leftUnitor
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} (w : ExchangeWord P Q) :
    ExchangeIso ((ExchangeWord.id P).comp w) w where
  top := Functor.leftUnitor _
  bot := Functor.leftUnitor _
  comm := by
    ext K
    simp [ExchangeWord.comp, ExchangeWord.id, TwoSquare.hComp]

private def properWord
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {v : X' ⟶ X} {b : Y' ⟶ Y} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (sq : CommSq v f' f b) :
    ExchangeWord D((v)^*[ModuleCat.{u + 1} A]) D((b)^*[ModuleCat.{u + 1} A]) where
  top := R((f)_*[ModuleCat.{u + 1} A])
  bot := R((f')_*[ModuleCat.{u + 1} A])
  exchange := exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq

private def openWord
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {v : X' ⟶ X} {b : Y' ⟶ Y} {j : X ⟶ Y} {j' : X' ⟶ Y'}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback v j' j b) :
    ExchangeWord D((v)^*[ModuleCat.{u + 1} A]) D((b)^*[ModuleCat.{u + 1} A]) where
  top := D((j)_!open[ModuleCat.{u + 1} A])
  bot := D((j')_!open[ModuleCat.{u + 1} A])
  exchange := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
    (ModuleCat.{u + 1} A) sq).inv

private def properComp
    (A : Type (u + 1)) [CommRing A]
    {U U' V V' Z Z' : Scheme.{u}}
    {t : U' ⟶ U} {m : V' ⟶ V} {b : Z' ⟶ Z}
    {l₁ : U' ⟶ V'} {r₁ : U ⟶ V} {l₂ : V' ⟶ Z'} {r₂ : V ⟶ Z}
    (sq₁ : CommSq t l₁ r₁ m) (sq₂ : CommSq m l₂ r₂ b) :
    ExchangeIso ((properWord A sq₁).comp (properWord A sq₂))
      (properWord A (sq₁.vert_comp sq₂)) where
  top := rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂
  bot := rightDerivedLowerStarComp (ModuleCat.{u + 1} A) l₁ l₂
  comm := by
    ext K
    simpa only [properWord, ExchangeWord.comp, TwoSquare.hComp, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] using
      sfExactExchangePasting.2.1 A sq₁ sq₂ K

private def properCompOfEq
    (A : Type (u + 1)) [CommRing A]
    {U U' V V' Z Z' : Scheme.{u}}
    {t : U' ⟶ U} {m : V' ⟶ V} {b : Z' ⟶ Z}
    {l₁ : U' ⟶ V'} {r₁ : U ⟶ V} {l₂ : V' ⟶ Z'} {r₂ : V ⟶ Z}
    (sq₁ : CommSq t l₁ r₁ m) (sq₂ : CommSq m l₂ r₂ b)
    (r : U ⟶ Z) (l : U' ⟶ Z') (hr : r₁ ≫ r₂ = r) (hl : l₁ ≫ l₂ = l)
    (sq : CommSq t l r b) :
    ExchangeIso ((properWord A sq₁).comp (properWord A sq₂)) (properWord A sq) where
  top := rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) r₁ r₂ r hr
  bot := rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) l₁ l₂ l hl
  comm := by
    subst r l
    exact (properComp A sq₁ sq₂).comm

private def openComp
    (A : Type (u + 1)) [CommRing A]
    {U U' V V' Z Z' : Scheme.{u}}
    {t : U' ⟶ U} {m : V' ⟶ V} {b : Z' ⟶ Z}
    {l₁ : U' ⟶ V'} {r₁ : U ⟶ V} {l₂ : V' ⟶ Z'} {r₂ : V ⟶ Z}
    [IsOpenImmersion l₁] [IsOpenImmersion r₁]
    [IsOpenImmersion l₂] [IsOpenImmersion r₂]
    (sq₁ : IsPullback t l₁ r₁ m) (sq₂ : IsPullback m l₂ r₂ b) :
    ExchangeIso ((openWord A sq₁).comp (openWord A sq₂))
      (openWord A (sq₁.paste_vert sq₂)) where
  top := (mapDerivedCategoryOpenImmersionLowerShriekComp
    (ModuleCat.{u + 1} A) r₁ r₂).symm
  bot := (mapDerivedCategoryOpenImmersionLowerShriekComp
    (ModuleCat.{u + 1} A) l₁ l₂).symm
  comm := by
    ext K
    simpa only [openWord, ExchangeWord.comp, TwoSquare.hComp, TwoSquare.mk,
      Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] using
      sfExactExchangePasting.2.2 A sq₁ sq₂ K

private def openCompOfEq
    (A : Type (u + 1)) [CommRing A]
    {U U' V V' Z Z' : Scheme.{u}}
    {t : U' ⟶ U} {m : V' ⟶ V} {b : Z' ⟶ Z}
    {l₁ : U' ⟶ V'} {r₁ : U ⟶ V} {l₂ : V' ⟶ Z'} {r₂ : V ⟶ Z}
    [IsOpenImmersion l₁] [IsOpenImmersion r₁]
    [IsOpenImmersion l₂] [IsOpenImmersion r₂]
    (sq₁ : IsPullback t l₁ r₁ m) (sq₂ : IsPullback m l₂ r₂ b)
    (r : U ⟶ Z) (l : U' ⟶ Z') (hr : r₁ ≫ r₂ = r) (hl : l₁ ≫ l₂ = l)
    [IsOpenImmersion r] [IsOpenImmersion l] (sq : IsPullback t l r b) :
    ExchangeIso ((openWord A sq₁).comp (openWord A sq₂)) (openWord A sq) where
  top := (mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} A) r₁ r₂).symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hr
  bot := (mapDerivedCategoryOpenImmersionLowerShriekComp
      (ModuleCat.{u + 1} A) l₁ l₂).symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hl
  comm := by
    subst r l
    simpa only [openComp, mapDerivedCategoryOpenImmersionLowerShriekCongr,
      Iso.trans_refl] using
      (openComp A sq₁ sq₂).comm

private def cartesianInterchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z U' V' W' Z' : Scheme.{u}}
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    {k' : U' ⟶ V'} {r' : U' ⟶ W'} {p' : V' ⟶ Z'} {i' : W' ⟶ Z'}
    {d : U' ⟶ U} {a : V' ⟶ V} {c : W' ⟶ W} {b : Z' ⟶ Z}
    [IsProper p] [IsProper r] [IsOpenImmersion i] [IsOpenImmersion k]
    [IsProper p'] [IsProper r'] [IsOpenImmersion i'] [IsOpenImmersion k']
    (sq : IsPullback r k i p) (sq' : IsPullback r' k' i' p')
    (sk : IsPullback d k' k a) (si : IsPullback c i' i b)
    (sp : IsPullback a p' p b) (sr : IsPullback d r' r c) :
    ExchangeIso ((properWord A sr.toCommSq).comp (openWord A si))
      ((openWord A sk).comp (properWord A sp.toCommSq)) where
  top := openImmersionLowerShriekLowerStarExchangeIso A sq
  bot := openImmersionLowerShriekLowerStarExchangeIso A sq'
  comm := by
    obtain ⟨θ, Γ, h⟩ := etaleProperOpenExchangeCube A
    have hc := h.2.2.2.2.2.2.2 k r p i k' r' p' i' d a c b
      sq.toCommSq.flip sq'.toCommSq.flip sk si sp sr
    rw [h.2.2.1 k r p i sq, h.2.2.1 k' r' p' i' sq'] at hc
    simpa only [ExchangeWord.comp, TwoSquare.hComp, TwoSquare.mk,
      properWord, openWord, openImmersionLowerShriekLowerStarExchangeIso, asIso_hom,
      Category.assoc] using hc

private theorem derivedOpenId_conjugate
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

private theorem leftAdjointId_compare
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

private theorem openId_normalization
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (unboundedFormalism A).shId X =
      mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X := by
  rw [ExchangeFormalism.shId]
  unfold mapDerivedCategoryOpenImmersionLowerShriekId openImmersionLowerShriekId
  rw [leftAdjointId_compare]
  apply conjugate_iso_symm_eq
  exact derivedOpenId_conjugate A X

private def openId
    (A : Type (u + 1)) [CommRing A] {X X' : Scheme.{u}} (v : X' ⟶ X) :
    ExchangeIso (openWord A (IsPullback.id_vert v))
      (ExchangeWord.id D((v)^*[ModuleCat.{u + 1} A])) where
  top := mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X
  bot := mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X'
  comm := by
    have h := (unboundedFormalism A).baseChange_id_vert v (by simp)
    have hh := unbounded_open_base_change A (IsPullback.id_vert v)
    rw [h] at hh
    simp only [openId_normalization, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.mk] at hh
    change Functor.whiskerLeft D((v)^*[ModuleCat.{u + 1} A])
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X').hom ≫
      ((Functor.rightUnitor D((v)^*[ModuleCat.{u + 1} A])).hom ≫
        (Functor.leftUnitor D((v)^*[ModuleCat.{u + 1} A])).inv) ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X).inv
        D((v)^*[ModuleCat.{u + 1} A]) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (IsPullback.id_vert v)).hom at hh
    ext K
    have hk := congr_app hh K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
      Category.id_comp, Category.comp_id] at hk
    simp only [openWord, ExchangeWord.id, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
      Category.id_comp, Category.comp_id, Functor.map_id]
    apply (cancel_epi ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) (IsPullback.id_vert v)).hom.app K)).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← hk]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Functor.map_id, Category.id_comp, Category.comp_id]
    change (mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} A) X').hom.app (D((v)^*[ModuleCat.{u + 1} A]).obj K) ≫
      𝟙 _ ≫ D((v)^*[ModuleCat.{u + 1} A]).map (𝟙 K) ≫ 𝟙 _ = _
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]
    exact (congrArg (fun q ↦ (mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} A) X').hom.app (D((v)^*[ModuleCat.{u + 1} A]).obj K) ≫ q)
      ((D((v)^*[ModuleCat.{u + 1} A])).map_id K)).trans (Category.comp_id _)

private theorem openCongr_inv
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    {j j' : X ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j') :
    (mapDerivedCategoryOpenImmersionLowerShriekCongr
      (ModuleCat.{u + 1} A) h).inv =
    (mapDerivedCategoryOpenImmersionLowerShriekCongr
      (ModuleCat.{u + 1} A) h.symm).hom := by
  subst j'
  rfl

/-- The identity-top Cartesian interchange, with the specified open identity removed. -/
private def graphTriangle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' U U' W W' : Scheme.{u}}
    {v : X' ⟶ X} {m : U' ⟶ U} {n : W' ⟶ W}
    {r : X ⟶ U} {r' : X' ⟶ U'} {h : X ⟶ W} {h' : X' ⟶ W'}
    {j : U ⟶ W} {j' : U' ⟶ W'}
    [IsProper r] [IsProper r'] [IsProper h] [IsProper h']
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sr : IsPullback v r' r m) (sh : IsPullback v h' h n)
    (sj : IsPullback m j' j n) (hr : r ≫ j = h) (hr' : r' ≫ j' = h') :
    ExchangeIso ((properWord A sr.toCommSq).comp (openWord A sj))
      (properWord A sh.toCommSq) := by
  let s : IsPullback r (𝟙 X) j h :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hr⟩
  let s' : IsPullback r' (𝟙 X') j' h' :=
    IsPullback.of_vert_isIso_mono ⟨by simpa using hr'⟩
  exact (cartesianInterchange A s s' (IsPullback.id_vert v) sj sh sr).trans
    (((openId A v).comp (ExchangeIso.refl (properWord A sh.toCommSq))).trans
      (ExchangeIso.leftUnitor (properWord A sh.toCommSq)))

private theorem pullbackMap_fst
    {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [HasPullback f g] [HasPullback f' g']
    (hf : CommSq a f' f c) (hg : IsPullback b g' g c) :
    IsPullback (pullback.map f' g' f g a b c hf.w.symm hg.w.symm)
      (pullback.fst f' g') (pullback.fst f g) a := by
  let m := pullback.map f' g' f g a b c hf.w.symm hg.w.symm
  have hm : m ≫ pullback.fst f g = pullback.fst f' g' ≫ a := by
    simp [m]
  apply IsPullback.of_isLimit' ⟨hm⟩
  refine PullbackCone.IsLimit.mk _ (fun s ↦
    pullback.lift s.snd
      (hg.lift (s.fst ≫ pullback.snd f g) (s.snd ≫ f') (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition,
          Category.assoc, hf.w, Category.assoc]))
      (by simp)) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, hm, pullback.lift_fst_assoc]
      exact s.condition.symm
    · simp [m]
  · intro s
    simp
  · intro s l hl₁ hl₂
    apply pullback.hom_ext
    · simpa using hl₂
    · apply hg.hom_ext
      · have h := congrArg (fun z ↦ z ≫ pullback.snd f g) hl₁
        simpa [m, Category.assoc] using h
      · simp only [Category.assoc, hg.lift_snd]
        rw [← pullback.condition, ← Category.assoc, hl₂]
        simp only [pullback.lift_fst_assoc]

private theorem pullbackMap_snd
    {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
    [HasPullback f g] [HasPullback f' g']
    (hf : IsPullback a f' f c) (hg : CommSq b g' g c) :
    IsPullback (pullback.map f' g' f g a b c hf.w.symm hg.w.symm)
      (pullback.snd f' g') (pullback.snd f g) b := by
  let m := pullback.map f' g' f g a b c hf.w.symm hg.w.symm
  have hm : m ≫ pullback.snd f g = pullback.snd f' g' ≫ b := by
    simp [m]
  apply IsPullback.of_isLimit' ⟨hm⟩
  refine PullbackCone.IsLimit.mk _ (fun s ↦
    pullback.lift
      (hf.lift (s.fst ≫ pullback.fst f g) (s.snd ≫ g') (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, s.condition,
          Category.assoc, hg.w, Category.assoc]))
      s.snd (by simp)) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · simp [m]
    · simp only [Category.assoc, hm, pullback.lift_snd_assoc]
      exact s.condition.symm
  · intro s
    simp
  · intro s l hl₁ hl₂
    apply pullback.hom_ext
    · apply hf.hom_ext
      · have h := congrArg (fun z ↦ z ≫ pullback.fst f g) hl₁
        simpa [m, Category.assoc] using h
      · simp only [Category.assoc, hf.lift_snd]
        rw [pullback.condition, ← Category.assoc, hl₂]
        simp only [pullback.lift_snd_assoc]
    · simpa using hl₂

/-- A single graph map commutes with the exchanges of its source and target words.
Source: Stacks Project, Tag 0F7F and the explicit `B1`, `B12`, inverse `B2` formula
(auxiliary; not a blueprint node).

Proof:
1. Pull back the product of the two proper ambient schemes and its two supporting opens.
   The pullback universal property identifies it with the product for the two pulled-back
   presentations. It also identifies the graph lifts and their intersection. This works
   for every supplied Cartesian representative, not only the chosen fibre product.
2. Give every word of proper direct images and open extensions its successive exchange:
   the exact unbounded proper mate and the inverse unit-normalized open mate. For a
   proper compositor, mate pasting and the canonical composite-adjunction comparison
   give compatibility of this exchange with composition. For an open compositor, expand
   the unit equation of open base change on both sides, use pullback associativity, and
   apply injectivity of the open-adjunction Hom bijection. Exactness descends that
   sheaf identity degreewise to unbounded complexes. The identity cases follow in the
   same way using the identity adjunction.
3. The Cartesian normalization in `etaleProperOpenExchangeCube` identifies each
   interchange in `locallyClosedGraphSide1`, `locallyClosedGraphMiddle`, and
   `locallyClosedGraphSide2` with its specified Gamma. Its cube equation is precisely
   compatibility with the exchanges of the two words. Compatibility is preserved by
   whiskering, composition, and inversion of the comparison: multiply the same equation
   by its inverse on the two ends. This does not invert any proper exchange.
4. Apply step 3 to B1, the intersection map B12, and inverse B2. Apply step 2 to the
   proper/open compositors and the removal of R(id)_*. Their product is exactly the
   normalized graph map written below, and the successive exchanges of its two endpoint
   words are exactly the two `etaleGraphPresentationExchange` maps. -/
theorem etaleGraphFromOpen_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (v : X' ⟶ X) (b : Y' ⟶ Y)
    (sq : IsPullback v f' f b)
    (t : EtaleGraphPresentation f) (t' : EtaleGraphPresentation f')
    (dt : t.BaseChange t' v b) :
    Functor.whiskerRight
        (etaleGraphOpenNormalization A c ≪≫ etaleGraphComparisonFromOpen A c t).hom
        D((b)^*[ModuleCat.{u + 1} A]) ≫ etaleGraphPresentationExchange A dt =
      etaleGraphPresentationExchange A
          (EtaleGraphPresentation.ofCompactificationBaseChange c sq) ≫
        Functor.whiskerLeft D((v)^*[ModuleCat.{u + 1} A])
          (etaleGraphOpenNormalization A (c.ofIsPullback sq) ≪≫
            etaleGraphComparisonFromOpen A (c.ofIsPullback sq) t').hom := by
  let c' := c.ofIsPullback sq
  let z : c'.Z ⟶ c.Z := pullback.fst c.g b
  have hi : IsPullback v c'.i c.i z := c.isPullback_i_ofIsPullback sq
  have hp : IsPullback z c'.g c.g b := (c.isPullback_g_ofIsPullback sq).flip
  let h := (Category.assoc t.a t.e t.p).trans (t.fac.trans c.comm)
  let h' := (Category.assoc t'.a t'.e t'.p).trans (t'.fac.trans c'.comm)
  let s₁ := locallyClosedGraphS₁ t.a t.e t.p c.i c.g h
  let s₂ := locallyClosedGraphS₂ t.a t.e t.p c.i c.g h
  let s₁₂ := locallyClosedGraphS₁₂ t.a t.e t.p c.i c.g h
  let s₁' := locallyClosedGraphS₁ t'.a t'.e t'.p c'.i c'.g h'
  let s₂' := locallyClosedGraphS₂ t'.a t'.e t'.p c'.i c'.g h'
  let s₁₂' := locallyClosedGraphS₁₂ t'.a t'.e t'.p c'.i c'.g h'
  let model := Classical.choice
    (etaleLocallyClosedGraphModel A t.a t.e t.p c.i c.g c.comm.symm t.fac)
  let model' := Classical.choice
    (etaleLocallyClosedGraphModel A t'.a t'.e t'.p c'.i c'.g c'.comm.symm t'.fac)
  let := model.properS₁
  let := model.properS₂
  let := model.properS₁₂
  let := model'.properS₁
  let := model'.properS₂
  let := model'.properS₁₂
  -- Base change the ambient product, both graph neighborhoods, and their intersection.
  let mT := pullback.map t'.p c'.g t.p c.g dt.w z b dt.pSquare.w.symm hp.w.symm
  have mp₁ : IsPullback mT (pullback.fst t'.p c'.g) (pullback.fst t.p c.g) dt.w :=
    pullbackMap_fst dt.pSquare.toCommSq hp
  have mp₂ : IsPullback mT (pullback.snd t'.p c'.g) (pullback.snd t.p c.g) z :=
    pullbackMap_snd dt.pSquare hp.toCommSq
  let m₁ := pullback.map (pullback.snd t'.p c'.g) c'.i
    (pullback.snd t.p c.g) c.i mT v z mp₂.w.symm hi.w.symm
  let m₂ := pullback.map (pullback.fst t'.p c'.g) t'.e
    (pullback.fst t.p c.g) t.e mT dt.u dt.w mp₁.w.symm dt.eSquare.w.symm
  have mb₁ : IsPullback m₁ (pullback.fst (pullback.snd t'.p c'.g) c'.i)
      (pullback.fst (pullback.snd t.p c.g) c.i) mT :=
    pullbackMap_fst mp₂.toCommSq hi
  have mq₁ : IsPullback m₁ (pullback.snd (pullback.snd t'.p c'.g) c'.i)
      (pullback.snd (pullback.snd t.p c.g) c.i) v :=
    pullbackMap_snd mp₂ hi.toCommSq
  have mb₂ : IsPullback m₂ (pullback.fst (pullback.fst t'.p c'.g) t'.e)
      (pullback.fst (pullback.fst t.p c.g) t.e) mT :=
    pullbackMap_fst mp₁.toCommSq dt.eSquare
  have mq₂ : IsPullback m₂ (pullback.snd (pullback.fst t'.p c'.g) t'.e)
      (pullback.snd (pullback.fst t.p c.g) t.e) dt.u :=
    pullbackMap_snd mp₁ dt.eSquare.toCommSq
  let m₁₂ := pullback.map _ _ _ _ m₁ m₂ mT mb₁.w.symm mb₂.w.symm
  have mu₁ : IsPullback m₁₂ (pullback.fst _ _) (pullback.fst _ _) m₁ :=
    pullbackMap_fst mb₁.toCommSq mb₂
  have mu₂ : IsPullback m₁₂ (pullback.snd _ _) (pullback.snd _ _) m₂ :=
    pullbackMap_snd mb₁ mb₂.toCommSq
  have hs₁q : s₁ ≫ pullback.snd _ _ = 𝟙 X := by simp [s₁, locallyClosedGraphS₁]
  have hs₂q : s₂ ≫ pullback.snd _ _ = t.a := by simp [s₂, locallyClosedGraphS₂]
  have hs₁q' : s₁' ≫ pullback.snd _ _ = 𝟙 X' := by simp [s₁', locallyClosedGraphS₁]
  have hs₂q' : s₂' ≫ pullback.snd _ _ = t'.a := by simp [s₂', locallyClosedGraphS₂]
  have hs₁₂u : s₁₂ ≫ pullback.fst _ _ = s₁ := by simp [s₁₂, s₁, s₂, locallyClosedGraphS₁₂]
  have hs₁₂u' : s₁₂' ≫ pullback.fst _ _ = s₁' := by
    simp [s₁₂', s₁', s₂', locallyClosedGraphS₁₂]
  have hs₁₂v : s₁₂ ≫ pullback.snd _ _ = s₂ := by simp [s₁₂, s₁, s₂, locallyClosedGraphS₁₂]
  have hs₁₂v' : s₁₂' ≫ pullback.snd _ _ = s₂' := by
    simp [s₁₂', s₁', s₂', locallyClosedGraphS₁₂]
  have hV : v ≫ locallyClosedGraphV t.a t.e t.p c.i c.g h =
      locallyClosedGraphV t'.a t'.e t'.p c'.i c'.g h' ≫ mT := by
    apply pullback.hom_ext
    · simp only [locallyClosedGraphV, mT, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc]
      rw [dt.aSquare.w_assoc, dt.eSquare.w]
    · simpa only [locallyClosedGraphV, mT, Category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc] using hi.w
  have hs₁ : v ≫ s₁ = s₁' ≫ m₁ := by
    apply pullback.hom_ext
    · simpa only [s₁, s₁', locallyClosedGraphS₁, m₁, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp] using hV
    · simp only [s₁, s₁', locallyClosedGraphS₁, m₁, Category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      exact (Category.id_comp v).symm
  have hs₂ : v ≫ s₂ = s₂' ≫ m₂ := by
    apply pullback.hom_ext
    · simpa only [s₂, s₂', locallyClosedGraphS₂, m₂, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp] using hV
    · simpa only [s₂, s₂', locallyClosedGraphS₂, m₂, Category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc] using dt.aSquare.w
  have hs₁₂ : v ≫ s₁₂ = s₁₂' ≫ m₁₂ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hs₁₂u, mu₁.w, ← Category.assoc, hs₁₂u']
      exact hs₁
    · simp only [Category.assoc]
      rw [hs₁₂v, mu₂.w, ← Category.assoc, hs₁₂v']
      exact hs₂
  have ss₁ : IsPullback v s₁' s₁ m₁ :=
    IsPullback.of_bot (by simpa only [hs₁q, hs₁q'] using IsPullback.id_vert v)
      hs₁ mq₁
  have ss₂ : IsPullback v s₂' s₂ m₂ :=
    IsPullback.of_bot (by simpa only [hs₂q, hs₂q'] using dt.aSquare) hs₂ mq₂
  have ss₁₂ : IsPullback v s₁₂' s₁₂ m₁₂ :=
    IsPullback.of_bot (by simpa only [hs₁₂u, hs₁₂u'] using ss₁) hs₁₂ mu₁
  let pT := pullback.fst t.p c.g ≫ t.p
  let pT' := pullback.fst t'.p c'.g ≫ t'.p
  have spT : IsPullback mT pT' pT b := mp₁.paste_vert dt.pSquare
  let Rid := properWord A (IsPullback.id_vert v).toCommSq
  let Jj := openWord A hi
  let Rc := properWord A hp.toCommSq
  let Ra := properWord A dt.aSquare.toCommSq
  let Je := openWord A dt.eSquare
  let Rp := properWord A dt.pSquare.toCommSq
  let Rs₁ := properWord A ss₁.toCommSq
  let Rs₂ := properWord A ss₂.toCommSq
  let Rs₁₂ := properWord A ss₁₂.toCommSq
  let Jb₁ := openWord A mb₁
  let Jb₂ := openWord A mb₂
  let Ju₁ := openWord A mu₁
  let Ju₂ := openWord A mu₂
  let Rh := properWord A spT.toCommSq
  let Rq₁ := properWord A mq₁.toCommSq
  let Rq₂ := properWord A mq₂.toCommSq
  let Rp₁ := properWord A mp₁.toCommSq
  let Rp₂ := properWord A mp₂.toCommSq
  let sideSquare₁ := (IsPullback.of_hasPullback (pullback.snd t.p c.g) c.i).flip
  let sideSquare₁' := (IsPullback.of_hasPullback (pullback.snd t'.p c'.g) c'.i).flip
  let sideSquare₂ := (IsPullback.of_hasPullback (pullback.fst t.p c.g) t.e).flip
  let sideSquare₂' := (IsPullback.of_hasPullback (pullback.fst t'.p c'.g) t'.e).flip
  let comp₁ := properCompOfEq A ss₁.toCommSq mq₁.toCommSq (𝟙 X) (𝟙 X')
    hs₁q hs₁q' (IsPullback.id_vert v).toCommSq
  let comp₂ := properCompOfEq A ss₂.toCommSq mq₂.toCommSq t.a t'.a
    hs₂q hs₂q' dt.aSquare.toCommSq
  let compT₁ := properCompOfEq A mp₂.toCommSq hp.toCommSq pT pT'
    pullback.condition.symm pullback.condition.symm spT.toCommSq
  let compT₂ := properCompOfEq A mp₁.toCommSq dt.pSquare.toCommSq pT pT'
    rfl rfl spT.toCommSq
  let ex₁ := cartesianInterchange A sideSquare₁ sideSquare₁' mb₁ hi mp₂ mq₁
  let ex₂ := cartesianInterchange A sideSquare₂ sideSquare₂' mb₂ dt.eSquare mp₁ mq₂
  -- Paste the two side interchanges and the common-intersection comparison.
  let side₁ : ExchangeIso (Rid.comp (Jj.comp Rc)) (Rs₁.comp (Jb₁.comp Rh)) :=
    (comp₁.symm.comp (ExchangeIso.refl (Jj.comp Rc))).trans
      ((ExchangeIso.associator Rs₁ Rq₁ (Jj.comp Rc)).trans
        ((ExchangeIso.refl Rs₁).comp
          ((ExchangeIso.associator Rq₁ Jj Rc).symm.trans
            ((ex₁.comp (ExchangeIso.refl Rc)).trans
              ((ExchangeIso.associator Jb₁ Rp₂ Rc).trans
                ((ExchangeIso.refl Jb₁).comp compT₁))))))
  let side₂ : ExchangeIso (Ra.comp (Je.comp Rp)) (Rs₂.comp (Jb₂.comp Rh)) :=
    (comp₂.symm.comp (ExchangeIso.refl (Je.comp Rp))).trans
      ((ExchangeIso.associator Rs₂ Rq₂ (Je.comp Rp)).trans
        ((ExchangeIso.refl Rs₂).comp
          ((ExchangeIso.associator Rq₂ Je Rp).symm.trans
            ((ex₂.comp (ExchangeIso.refl Rp)).trans
              ((ExchangeIso.associator Jb₂ Rp₁ Rp).trans
                ((ExchangeIso.refl Jb₂).comp compT₂))))))
  let triangle₁ := graphTriangle A ss₁₂ ss₁ mu₁ hs₁₂u hs₁₂u'
  let triangle₂ := graphTriangle A ss₁₂ ss₂ mu₂ hs₁₂v hs₁₂v'
  let openComp₁ := openComp A mu₁ mb₁
  let compositeOpenSquare := mu₁.paste_vert mb₁
  let openComp₂ := openCompOfEq A mu₂ mb₂ _ _
    pullback.condition.symm pullback.condition.symm compositeOpenSquare
  let middleSmall : ExchangeIso (Rs₁.comp Jb₁) (Rs₂.comp Jb₂) :=
    (triangle₁.symm.comp (ExchangeIso.refl Jb₁)).trans
      ((ExchangeIso.associator Rs₁₂ Ju₁ Jb₁).trans
        (((ExchangeIso.refl Rs₁₂).comp (openComp₁.trans openComp₂.symm)).trans
          ((ExchangeIso.associator Rs₁₂ Ju₂ Jb₂).symm.trans
            (triangle₂.comp (ExchangeIso.refl Jb₂)))))
  let middle : ExchangeIso (Rs₁.comp (Jb₁.comp Rh)) (Rs₂.comp (Jb₂.comp Rh)) :=
    (ExchangeIso.associator Rs₁ Jb₁ Rh).symm.trans
      ((middleSmall.comp (ExchangeIso.refl Rh)).trans
        (ExchangeIso.associator Rs₂ Jb₂ Rh))
  let comparison := side₁.trans (middle.trans side₂.symm)
  have hc := comparison.comm
  -- Identify the pasted maps with the fixed formula, including its identity normalization.
  have htop : comparison.top =
      etaleGraphOpenNormalization A c ≪≫ etaleGraphComparisonFromOpen A c t := by
    apply Iso.ext
    ext M
    simp only [comparison, side₁, side₂, middle, middleSmall, triangle₁, triangle₂,
      comp₁, comp₂, compT₁, compT₂, ex₁, ex₂, openComp₁, openComp₂,
      ExchangeIso.trans, ExchangeIso.comp, ExchangeIso.symm, ExchangeIso.refl,
      ExchangeIso.associator, ExchangeIso.leftUnitor,
      properCompOfEq, openComp, openCompOfEq, graphTriangle, cartesianInterchange, openId,
      Rid, Jj, Rc, Ra, Je, Rp, Rs₁, Rs₂, Rs₁₂, Jb₁, Jb₂, Ju₁, Ju₂, Rh, Rq₁, Rq₂, Rp₁, Rp₂,
      ExchangeWord.comp, properWord, openWord, EtaleGraphPresentation.ofCompactification,
      pT, pT', s₁, s₂, s₁₂, s₁', s₂', s₁₂',
      sideSquare₁, sideSquare₂, sideSquare₁', sideSquare₂',
      etaleGraphOpenNormalization, etaleGraphComparisonFromOpen, locallyClosedGraphIso,
      locallyClosedGraphSide₁, locallyClosedGraphSide₂, locallyClosedGraphMiddle,
      rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
      Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
      Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, Iso.trans_inv,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, openCongr_inv,
      Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
      Functor.map_comp, Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
      Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  have hbot : comparison.bot =
      etaleGraphOpenNormalization A c' ≪≫ etaleGraphComparisonFromOpen A c' t' := by
    apply Iso.ext
    ext M
    simp only [comparison, side₁, side₂, middle, middleSmall, triangle₁, triangle₂,
      comp₁, comp₂, compT₁, compT₂, ex₁, ex₂, openComp₁, openComp₂,
      ExchangeIso.trans, ExchangeIso.comp, ExchangeIso.symm, ExchangeIso.refl,
      ExchangeIso.associator, ExchangeIso.leftUnitor,
      properCompOfEq, openComp, openCompOfEq, graphTriangle, cartesianInterchange, openId,
      Rid, Jj, Rc, Ra, Je, Rp, Rs₁, Rs₂, Rs₁₂, Jb₁, Jb₂, Ju₁, Ju₂, Rh, Rq₁, Rq₂, Rp₁, Rp₂,
      ExchangeWord.comp, properWord, openWord, EtaleGraphPresentation.ofCompactification,
      pT, pT', s₁, s₂, s₁₂, s₁', s₂', s₁₂',
      sideSquare₁, sideSquare₂, sideSquare₁', sideSquare₂',
      etaleGraphOpenNormalization, etaleGraphComparisonFromOpen, locallyClosedGraphIso,
      locallyClosedGraphSide₁, locallyClosedGraphSide₂, locallyClosedGraphMiddle,
      rightDerivedLowerStarCompOpenImmersionLowerShriekIso,
      Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
      Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, Iso.trans_inv,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, openCongr_inv,
      Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
      Functor.map_comp, Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
      Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  rw [htop, hbot] at hc
  simpa only [Rid, Jj, Rc, Ra, Je, Rp, ExchangeWord.comp, properWord, openWord,
    TwoSquare.hComp, TwoSquare.mk,
    etaleGraphPresentationExchange, EtaleGraphPresentation.ofCompactificationBaseChange,
    EtaleGraphPresentation.functor, EtaleGraphPresentation.ofCompactification, c', z]
    using hc

end AlgebraicGeometry.Etale
