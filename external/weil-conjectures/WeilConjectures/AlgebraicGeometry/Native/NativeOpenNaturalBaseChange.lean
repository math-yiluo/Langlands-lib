/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square

import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction
import WeilConjectures.WeilSheaf.DirectImageRestriction
import WeilConjectures.WeilSheaf.IsotypicPullback

/-!
# Native Weil open base change

The assertion is the natural base-change isomorphism for the actual native extension by
zero and pullback functors on the ordinary derived categories of all native Weil sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

-- The mate component and native carrier calculations below follow the proved private
-- helpers of WeilConjectures.WeilSheaf.Native.Open.NativeOpenProperInterchange.
-- Only the heart comparison is needed here; the proper/open theorem and its additional
-- imports are not used.
namespace CategoryTheory

private theorem inverseMate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (M : C) :
    (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ β)).app M) =
      L₂.map (G.map (a₁.unit.app M)) ≫
        L₂.map (β.app (L₁.obj M)) ≫ a₂.counit.app (H.obj (L₁.obj M)) := by
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_id, Category.id_comp]
  change _ ≫ _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]

private noncomputable def inverseMateNatTrans
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) : G ⋙ L₂ ⟶ L₁ ⋙ H where
  app M := L₂.map (G.map (a₁.unit.app M)) ≫
    L₂.map (β.app (L₁.obj M)) ≫ a₂.counit.app (H.obj (L₁.obj M))
  naturality M N f := by
    have h := (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ β))).naturality f
    simpa only [inverseMate_app] using h

end CategoryTheory

namespace AlgebraicGeometry

private noncomputable def nativeOpenAdjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j := by
  apply IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

attribute [local irreducible] nativeOpenAdjunction

private noncomputable def nativeOpenBaseChangeMap
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {V U P X : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
    [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    (sq : CommSq q b j p) :
    ProEtaleWeilSheaf.lowerStar k₀ l p ⋙ ProEtaleWeilSheaf.upperStar k₀ l j ⟶
      ProEtaleWeilSheaf.upperStar k₀ l b ⋙ ProEtaleWeilSheaf.lowerStar k₀ l q :=
  inverseMateNatTrans (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l b)
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j)
    (ProEtaleWeilSheaf.lowerStarSquareIso k₀ l sq.w.symm).hom

@[reassoc]
private theorem adicLowerStarCongr_trans
    (l : ℕ) [Fact l.Prime] {P X : Scheme.{u}} {f g h : P ⟶ X}
    (e : f = g) (e' : g = h) (M : ProEtale.AdicSheaf l P) :
    (ProEtale.adicLowerStarCongr l e).hom.app M ≫
      (ProEtale.adicLowerStarCongr l e').hom.app M =
        (ProEtale.adicLowerStarCongr l (e.trans e')).hom.app M := by
  subst e
  subst e'
  apply Mod.hom_ext
  simp only [Mod.comp_hom', ProEtale.adicLowerStarCongr_hom_app_hom,
    ProEtale.lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

private theorem adicLowerStarCongr_inv
    (l : ℕ) [Fact l.Prime] {P X : Scheme.{u}} {f g : P ⟶ X}
    (e : f = g) (M : ProEtale.AdicSheaf l P) :
    (ProEtale.adicLowerStarCongr l e).inv.app M =
      (ProEtale.adicLowerStarCongr l e.symm).hom.app M := by
  subst e
  apply Mod.hom_ext
  rfl

private theorem nativeLowerStarSquareIso_underlying
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {V U P X : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
    [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    (sq : CommSq q b j p) (M : ProEtaleWeilSheaf k₀ l V) :
    ((ProEtaleWeilSheaf.lowerStarSquareIso k₀ l sq.w.symm).hom.app M).hom.f =
      (ProEtale.adicSquareLowerStarIso l
        (CommSq.mk (show Scheme.Hom.geometricFiberMap q (comp_over q _) ≫
            Scheme.Hom.geometricFiberMap j (comp_over j _) =
          Scheme.Hom.geometricFiberMap b (comp_over b _) ≫
            Scheme.Hom.geometricFiberMap p (comp_over p _) by
          rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
          exact Scheme.Hom.geometricFiberMap_congr sq.w _ _))).hom.app M.carrier := by
  simp only [ProEtaleWeilSheaf.lowerStarSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, IsoAlgebra.comp_hom_f,
    ProEtaleWeilSheaf.lowerStarCompIso_hom_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCompIso_inv_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCongr_hom_app_hom_f,
    Iso.trans_inv, ProEtale.adicSquareLowerStarIso]
  simp only [Category.assoc, adicLowerStarCongr_inv]
  rw [adicLowerStarCongr_trans_assoc, adicLowerStarCongr_trans_assoc]

private theorem nativeUpperStar_map_hom_f
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {V P : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [P.Over (Spec (CommRingCat.of k₀))]
    (b : V ⟶ P) [b.IsOver (Spec (CommRingCat.of k₀))]
    {M N : ProEtaleWeilSheaf k₀ l P} (f : M ⟶ N) :
    ((ProEtaleWeilSheaf.upperStar k₀ l b).map f).hom.f =
      (ProEtale.adicUpperStar l (Scheme.Hom.geometricFiberMap b (comp_over b _))).map
        f.hom.f := rfl

section NativeOpenBaseChange

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {V U P X : Scheme.{u}}
  [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
  [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
  [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
  [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
  [IsOpenImmersion b] [IsOpenImmersion j]

omit [IsOpenImmersion b] [IsOpenImmersion j] in
private theorem nativeOpenBaseChangeMap_underlying (sq : CommSq q b j p)
    (M : ProEtaleWeilSheaf k₀ l P) :
    ((nativeOpenBaseChangeMap k₀ l q b j p sq).app M).hom.f =
      (ProEtale.adicBaseChangeMap l
        (CommSq.mk (show Scheme.Hom.geometricFiberMap q (comp_over q _) ≫
            Scheme.Hom.geometricFiberMap j (comp_over j _) =
          Scheme.Hom.geometricFiberMap b (comp_over b _) ≫
            Scheme.Hom.geometricFiberMap p (comp_over p _) by
          rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
          exact Scheme.Hom.geometricFiberMap_congr sq.w _ _))).app M.carrier := by
  simp only [nativeOpenBaseChangeMap, inverseMateNatTrans,
    ProEtale.adicBaseChangeMap, inverseMate_app,
    IsoAlgebra.comp_hom_f, ProEtaleWeilSheaf.lowerStar_map_hom_f,
    nativeUpperStar_map_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f]
  rw [nativeLowerStarSquareIso_underlying k₀ l q b j p sq]
  rfl

attribute [local irreducible] nativeOpenBaseChangeMap

private theorem nativeOpenBaseChangeMap_isIso (hsq : IsPullback q b j p) :
    IsIso (nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq) := by
  have hgeo := Scheme.Hom.isPullback_geometricFiberMap_of_isPullback (k := k₀) hsq
    (comp_over q _) (comp_over b _) (comp_over j _) (comp_over p _)
  have := ProEtale.isIso_adicBaseChangeMap_of_isPullback l hgeo
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso ((IsoAlgebra.forget _).map
      ((nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq).app M)) := by
    change IsIso (((nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq).app M).hom.f)
    rw [nativeOpenBaseChangeMap_underlying]
    infer_instance
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

end NativeOpenBaseChange

/-- The exact derived comparison, keeping the construction's auxiliary proofs private. -/
private noncomputable def nativeOpenDerivedBaseChangeIso
    (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {U' U T' T : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))]
    [T'.Over (Spec (CommRingCat.of k₀))]
    [T.Over (Spec (CommRingCat.of k₀))]
    (v : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (u : T' ⟶ T)
    [v.IsOver (Spec (CommRingCat.of k₀))]
    [j'.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    [u.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [IsOpenImmersion j]
    (hsq : IsPullback v j' j u) :
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l u).mapDerivedCategory ≅
      (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory := by
  have := nativeOpenBaseChangeMap_isIso k₀ l v j' j u hsq
  let e := asIso (nativeOpenBaseChangeMap k₀ l v j' j u hsq.toCommSq)
  let adj := ((nativeOpenAdjunction k₀ l j).comp
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l u)).ofNatIsoRight e
  let adj' := (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l v).comp
    (nativeOpenAdjunction k₀ l j')
  exact Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointUniq adj adj') ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

attribute [local irreducible] nativeOpenDerivedBaseChangeIso

/-- Pullback commutes with native extension by zero in a Cartesian open square. -/
theorem nativeWeilOpenNaturalBaseChange
    (k₀ : Type u) [Field k₀] [Finite k₀]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {U' U T' T : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))]
    [T'.Over (Spec (CommRingCat.of k₀))]
    [T.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    (v : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (u : T' ⟶ T)
    [v.IsOver (Spec (CommRingCat.of k₀))]
    [j'.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    [u.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [IsOpenImmersion j] [QuasiCompact j]
    (sq : ChosenCartesianSquare v j' j u) :
    Nonempty
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.upperStar k₀ l u).mapDerivedCategory ≅
        (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory) := by
  exact ⟨nativeOpenDerivedBaseChangeIso k₀ l v j' j u
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)⟩

end AlgebraicGeometry
