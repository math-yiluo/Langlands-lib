/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeBaseChange.GeometricProperBaseChange
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedForgetMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube

/-!
# Forgetting the canonical native derived base-change mate
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Endofunctor

namespace AlgebraicGeometry.NativeBaseChange

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

/-- Exact forgetting on ordinary unbounded derived categories. -/
abbrev forget (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :=
  (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory

variable {Z' Z T' T : Scheme.{u}}
  [Z'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [T'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
  {v : Z' ⟶ Z} {p' : Z' ⟶ T'} {p : Z ⟶ T} {g : T' ⟶ T}
  [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
  [p.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]

/-- The localized native composition comparison around a commutative square. -/
def pullSquare (sq : CommSq v p' p g) :
    (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l p').mapDerivedCategory ≅
      (ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      ((ProEtaleWeilSheaf.upperStarCompIso k₀ l p' g).symm ≪≫
        ProEtaleWeilSheaf.upperStarCongrIso k₀ l sq.w.symm ≪≫
        ProEtaleWeilSheaf.upperStarCompIso k₀ l v p) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

@[irreducible] private def abelianPullSquare (sq : CommSq v p' p g) :
    ProEtaleWeilSheaf.upperStar k₀ l g ⋙ ProEtaleWeilSheaf.upperStar k₀ l p' ≅
      ProEtaleWeilSheaf.upperStar k₀ l p ⋙ ProEtaleWeilSheaf.upperStar k₀ l v :=
  (ProEtaleWeilSheaf.upperStarCompIso k₀ l p' g).symm ≪≫
    ProEtaleWeilSheaf.upperStarCongrIso k₀ l sq.w.symm ≪≫
    ProEtaleWeilSheaf.upperStarCompIso k₀ l v p

private theorem abelianPullSquare_hom (sq : CommSq v p' p g) :
    (abelianPullSquare k₀ l sq).hom =
      (ProEtaleWeilSheaf.upperStarCompIso k₀ l p' g).inv ≫
        (ProEtaleWeilSheaf.upperStarCongrIso k₀ l sq.w.symm).hom ≫
        (ProEtaleWeilSheaf.upperStarCompIso k₀ l v p).hom := by
  unfold abelianPullSquare
  rfl

@[irreducible] private def abelianPullForget {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf.upperStar k₀ l f ⋙
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y) ⋙
        ProEtale.adicUpperStar l (geometricMap k₀ f) :=
  IsoAlgebra.mapOfNatIsoCompForgetIso
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l f
      (comp_over f (Spec (CommRingCat.of k₀))))

private theorem pullSquare_eq (sq : CommSq v p' p g) :
    pullSquare k₀ l sq = Functor.mapDerivedCategorySquareIso (abelianPullSquare k₀ l sq) := by
  unfold pullSquare abelianPullSquare
  rfl

omit [Finite k₀] in
private theorem geometricDerivedSquare_eq (sq : CommSq v p' p g) :
    ProEtale.adicDerivedPullSquare l (geometricSquare k₀ sq) =
      Functor.mapDerivedCategorySquareIso
        (ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm) := by
  rfl

private theorem transported_comp_inv_nat {C D E : Type*}
    [Category C] [Category D] [Category E]
    {F : C ⥤ C} {G : D ⥤ D} {H : E ⥤ E}
    {L₁ : C ⥤ D} {L₂ : D ⥤ E} {L : C ⥤ E}
    (e₁ : L₁ ⋙ G ≅ F ⋙ L₁) (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) {e : L ⋙ H ≅ F ⋙ L}
    (α : L₁ ⋙ L₂ ≅ L)
    (hα : Functor.whiskerRight α.hom H ≫ e.hom =
      (IsoAlgebra.compCommIso e₁ e₂).hom ≫ Functor.whiskerLeft F α.hom) :
    Functor.whiskerRight (IsoAlgebra.mapOfNatIsoCompForgetIso e₁).inv L₂ ≫
        Functor.whiskerLeft (IsoAlgebra.mapOfNatIso e₁)
          (IsoAlgebra.mapOfNatIsoCompForgetIso e₂).inv ≫
        Functor.whiskerRight
          ((IsoAlgebra.mapOfNatIsoIsoOfIso α hα).symm ≪≫
            (IsoAlgebra.mapOfNatIsoCompIso e₁ e₂).symm).inv (IsoAlgebra.forget H) =
      Functor.whiskerLeft (IsoAlgebra.forget F) α.hom ≫
        (IsoAlgebra.mapOfNatIsoCompForgetIso e).inv := by
  apply NatTrans.ext
  funext M
  change L₂.map (𝟙 _) ≫ 𝟙 _ ≫ (𝟙 _ ≫ α.hom.app M.carrier) =
    α.hom.app M.carrier ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private theorem transported_comp_hom_nat {C D E : Type*}
    [Category C] [Category D] [Category E]
    {F : C ⥤ C} {G : D ⥤ D} {H : E ⥤ E}
    {L₁ : C ⥤ D} {L₂ : D ⥤ E} {L : C ⥤ E}
    (e₁ : L₁ ⋙ G ≅ F ⋙ L₁) (e₂ : L₂ ⋙ H ≅ G ⋙ L₂) {e : L ⋙ H ≅ F ⋙ L}
    (α : L₁ ⋙ L₂ ≅ L)
    (hα : Functor.whiskerRight α.hom H ≫ e.hom =
      (IsoAlgebra.compCommIso e₁ e₂).hom ≫ Functor.whiskerLeft F α.hom) :
    (IsoAlgebra.mapOfNatIsoCompForgetIso e).inv ≫
        Functor.whiskerRight
          ((IsoAlgebra.mapOfNatIsoIsoOfIso α hα).symm ≪≫
            (IsoAlgebra.mapOfNatIsoCompIso e₁ e₂).symm).hom (IsoAlgebra.forget H) =
      Functor.whiskerLeft (IsoAlgebra.forget F) α.inv ≫
        Functor.whiskerRight (IsoAlgebra.mapOfNatIsoCompForgetIso e₁).inv L₂ ≫
        Functor.whiskerLeft (IsoAlgebra.mapOfNatIso e₁)
          (IsoAlgebra.mapOfNatIsoCompForgetIso e₂).inv := by
  apply NatTrans.ext
  funext M
  change 𝟙 _ ≫ (α.inv.app M.carrier ≫ 𝟙 _) =
    α.inv.app M.carrier ≫ L₂.map (𝟙 _) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [Category.comp_id]

private theorem comp_inv_forget_nat {A B C : Scheme.{u}}
    [A.Over (Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))] (f : A ⟶ B) (h : B ⟶ C)
    [f.IsOver (Spec (CommRingCat.of k₀))] [h.IsOver (Spec (CommRingCat.of k₀))] :
    Functor.whiskerRight (abelianPullForget k₀ l h).inv
        (ProEtale.adicUpperStar l (geometricMap k₀ f)) ≫
      Functor.whiskerLeft (ProEtaleWeilSheaf.upperStar k₀ l h)
        (abelianPullForget k₀ l f).inv ≫
      Functor.whiskerRight (ProEtaleWeilSheaf.upperStarCompIso k₀ l f h).inv
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l A)) =
    Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l C))
        (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l f h).hom ≫
      (abelianPullForget k₀ l (f ≫ h)).inv := by
  unfold abelianPullForget ProEtaleWeilSheaf.upperStarCompIso
  dsimp only [ProEtaleWeilSheaf.upperStar]
  have hh := transported_comp_inv_nat
    (F := WeilSheaf.frobeniusPullback k₀ l C)
    (G := WeilSheaf.frobeniusPullback k₀ l B)
    (H := WeilSheaf.frobeniusPullback k₀ l A)
    (L₁ := ProEtale.adicUpperStar l (geometricMap k₀ h))
    (L₂ := ProEtale.adicUpperStar l (geometricMap k₀ f))
    (L := ProEtale.adicUpperStar l (geometricMap k₀ (f ≫ h)))
    (e := ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l (f ≫ h)
      (comp_over (f ≫ h) (Spec (CommRingCat.of k₀))))
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l h
      (comp_over h (Spec (CommRingCat.of k₀))))
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l f
      (comp_over f (Spec (CommRingCat.of k₀))))
    (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l f h)
    (ProEtaleWeilSheaf.upperStarComp_exchange (k₀ := k₀) (l := l) f h)
  with_reducible exact hh

private theorem comp_hom_forget_nat {A B C : Scheme.{u}}
    [A.Over (Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))] (f : A ⟶ B) (h : B ⟶ C)
    [f.IsOver (Spec (CommRingCat.of k₀))] [h.IsOver (Spec (CommRingCat.of k₀))] :
    (abelianPullForget k₀ l (f ≫ h)).inv ≫
      Functor.whiskerRight (ProEtaleWeilSheaf.upperStarCompIso k₀ l f h).hom
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l A)) =
    Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l C))
        (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l f h).inv ≫
      Functor.whiskerRight (abelianPullForget k₀ l h).inv
        (ProEtale.adicUpperStar l (geometricMap k₀ f)) ≫
      Functor.whiskerLeft (ProEtaleWeilSheaf.upperStar k₀ l h)
        (abelianPullForget k₀ l f).inv := by
  unfold abelianPullForget ProEtaleWeilSheaf.upperStarCompIso
  dsimp only [ProEtaleWeilSheaf.upperStar]
  have hh := transported_comp_hom_nat
    (F := WeilSheaf.frobeniusPullback k₀ l C)
    (G := WeilSheaf.frobeniusPullback k₀ l B)
    (H := WeilSheaf.frobeniusPullback k₀ l A)
    (L₁ := ProEtale.adicUpperStar l (geometricMap k₀ h))
    (L₂ := ProEtale.adicUpperStar l (geometricMap k₀ f))
    (L := ProEtale.adicUpperStar l (geometricMap k₀ (f ≫ h)))
    (e := ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l (f ≫ h)
      (comp_over (f ≫ h) (Spec (CommRingCat.of k₀))))
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l h
      (comp_over h (Spec (CommRingCat.of k₀))))
    (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l f
      (comp_over f (Spec (CommRingCat.of k₀))))
    (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l f h)
    (ProEtaleWeilSheaf.upperStarComp_exchange (k₀ := k₀) (l := l) f h)
  with_reducible exact hh

private theorem congr_forget_nat {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    {f f' : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
    [f'.IsOver (Spec (CommRingCat.of k₀))] (h : f = f')
    (hg : geometricMap k₀ f = geometricMap k₀ f') :
    (abelianPullForget k₀ l f).inv ≫
        Functor.whiskerRight (ProEtaleWeilSheaf.upperStarCongrIso k₀ l h).hom
          (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) =
      Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
        (ProEtale.adicUpperStarCongr l hg).hom ≫
        (abelianPullForget k₀ l f').inv := by
  subst h
  simp only [ProEtaleWeilSheaf.upperStarCongrIso, ProEtale.adicUpperStarCongr,
    eqToIso_refl, Iso.refl_hom, Functor.whiskerRight_id', Functor.whiskerLeft_id',
    Category.id_comp, Category.comp_id]

omit [Finite k₀] in
private theorem geometric_pullSquare (sq : CommSq v p' p g)
    (hw : geometricMap k₀ (p' ≫ g) = geometricMap k₀ (v ≫ p)) :
    adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l p' g ≪≫
        ProEtale.adicUpperStarCongr l hw ≪≫
        (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l v p).symm =
      ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm := by
  have hm :
      (ProEtale.adicUpperStarCongr l
        (Scheme.Hom.geometricFiberMap_comp p' g
          (comp_over p' (Spec (CommRingCat.of k₀)))
          (comp_over g (Spec (CommRingCat.of k₀)))).symm ≪≫
        ProEtale.adicUpperStarCongr l hw ≪≫
        (ProEtale.adicUpperStarCongr l
          (Scheme.Hom.geometricFiberMap_comp v p
            (comp_over v (Spec (CommRingCat.of k₀)))
            (comp_over p (Spec (CommRingCat.of k₀)))).symm).symm) =
      ProEtale.adicUpperStarCongr l (geometricSquare k₀ sq).w.symm := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, ProEtale.adicUpperStarCongr,
      eqToIso.hom, eqToIso.inv, eqToHom_trans]
  have hh := congrArg (fun e ↦
    (ProEtale.adicUpperStarComp l (geometricMap k₀ p')
      (geometricMap k₀ g)).symm ≪≫ e ≪≫
      ProEtale.adicUpperStarComp l (geometricMap k₀ v) (geometricMap k₀ p)) hm
  simpa only [adicUpperStarGeometricFiberMapCompIso, ProEtale.adicUpperStarCompIso,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc] using hh

private theorem whiskerLeft_iso_paste {C D E : Type*}
    [Category C] [Category D] [Category E] (U : C ⥤ D)
    {F G H I : D ⥤ E} (a : F ≅ G) (b : G ≅ H) (c : H ≅ I) (w : F ≅ I)
    (h : a ≪≫ b ≪≫ c = w) :
    Functor.whiskerLeft U a.hom ≫ Functor.whiskerLeft U b.hom ≫
        Functor.whiskerLeft U c.hom = Functor.whiskerLeft U w.hom := by
  have hh := congrArg (fun e ↦ Functor.whiskerLeft U e.hom) h
  simpa only [Iso.trans_hom, Functor.whiskerLeft_comp] using hh

private theorem geometric_pullSquare_nat (sq : CommSq v p' p g)
    (hw : geometricMap k₀ (p' ≫ g) = geometricMap k₀ (v ≫ p)) :
    Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
        (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l p' g).hom ≫
      Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
        (ProEtale.adicUpperStarCongr l hw).hom ≫
      Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
        (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l v p).inv =
      Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
        (ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm).hom := by
  exact whiskerLeft_iso_paste
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
    (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l p' g)
    (ProEtale.adicUpperStarCongr l hw)
    (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l v p).symm
    (ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm)
    (geometric_pullSquare k₀ l sq hw)

private theorem whiskered_square_paste {C D E : Type*}
    [Category C] [Category D] [Category E] (U : D ⥤ E)
    {N₁ N₂ N₃ N₄ : C ⥤ D} {X Y Z₁ Z₂ Z₃ Z₄ : C ⥤ E}
    {r : N₁ ⟶ N₄} {r₁ : N₁ ⟶ N₂} {r₂ : N₂ ⟶ N₃} {r₃ : N₃ ⟶ N₄}
    {a : X ⟶ Y} {b : Y ⟶ N₁ ⋙ U} {x : X ⟶ Z₁} {t : Z₁ ⟶ N₂ ⋙ U}
    {y : Z₁ ⟶ Z₂} {s : Z₂ ⟶ N₃ ⋙ U} {z : Z₂ ⟶ Z₃}
    {j : Z₃ ⟶ Z₄} {q : Z₄ ⟶ N₄ ⋙ U} {w : X ⟶ Z₃}
    (h_r : r = r₁ ≫ r₂ ≫ r₃)
    (h₁ : a ≫ b ≫ Functor.whiskerRight r₁ U = x ≫ t)
    (h₂ : t ≫ Functor.whiskerRight r₂ U = y ≫ s)
    (h₃ : s ≫ Functor.whiskerRight r₃ U = z ≫ j ≫ q)
    (h₄ : x ≫ y ≫ z = w) :
    a ≫ b ≫ Functor.whiskerRight r U = w ≫ j ≫ q := by
  rw [h_r]
  simp only [Functor.whiskerRight_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄]

private theorem abelianPullSquare_cube_nat (sq : CommSq v p' p g) :
    Functor.whiskerRight (abelianPullForget k₀ l g).inv
        (ProEtale.adicUpperStar l (geometricMap k₀ p')) ≫
      Functor.whiskerLeft (ProEtaleWeilSheaf.upperStar k₀ l g)
        (abelianPullForget k₀ l p').inv ≫
      Functor.whiskerRight (abelianPullSquare k₀ l sq).hom
        (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z')) =
    Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
        (ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm).hom ≫
      Functor.whiskerRight (abelianPullForget k₀ l p).inv
        (ProEtale.adicUpperStar l (geometricMap k₀ v)) ≫
      Functor.whiskerLeft (ProEtaleWeilSheaf.upperStar k₀ l p)
        (abelianPullForget k₀ l v).inv := by
  have hw : geometricMap k₀ (p' ≫ g) = geometricMap k₀ (v ≫ p) := by
    congr 1
    exact sq.w.symm
  exact @whiskered_square_paste
    (ProEtaleWeilSheaf k₀ l T) (ProEtaleWeilSheaf k₀ l Z')
    (ProEtale.AdicSheaf l (Z' ↘ Spec (CommRingCat.of k₀)).geometricFiber) _ _ _
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z'))
    (ProEtaleWeilSheaf.upperStar k₀ l g ⋙ ProEtaleWeilSheaf.upperStar k₀ l p')
    (ProEtaleWeilSheaf.upperStar k₀ l (p' ≫ g))
    (ProEtaleWeilSheaf.upperStar k₀ l (v ≫ p))
    (ProEtaleWeilSheaf.upperStar k₀ l p ⋙ ProEtaleWeilSheaf.upperStar k₀ l v)
    ((IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T) ⋙
        ProEtale.adicUpperStar l (geometricMap k₀ g)) ⋙
      ProEtale.adicUpperStar l (geometricMap k₀ p'))
    ((ProEtaleWeilSheaf.upperStar k₀ l g ⋙
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T')) ⋙
      ProEtale.adicUpperStar l (geometricMap k₀ p'))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T) ⋙
      ProEtale.adicUpperStar l (geometricMap k₀ (p' ≫ g)))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T) ⋙
      ProEtale.adicUpperStar l (geometricMap k₀ (v ≫ p)))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T) ⋙
      (ProEtale.adicUpperStar l (geometricMap k₀ p) ⋙
        ProEtale.adicUpperStar l (geometricMap k₀ v)))
    ((ProEtaleWeilSheaf.upperStar k₀ l p ⋙
        IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)) ⋙
      ProEtale.adicUpperStar l (geometricMap k₀ v))
    ((abelianPullSquare k₀ l sq).hom)
    ((ProEtaleWeilSheaf.upperStarCompIso k₀ l p' g).inv)
    ((ProEtaleWeilSheaf.upperStarCongrIso k₀ l sq.w.symm).hom)
    ((ProEtaleWeilSheaf.upperStarCompIso k₀ l v p).hom)
    (Functor.whiskerRight (abelianPullForget k₀ l g).inv
      (ProEtale.adicUpperStar l (geometricMap k₀ p')))
    (Functor.whiskerLeft (ProEtaleWeilSheaf.upperStar k₀ l g)
      (abelianPullForget k₀ l p').inv)
    (Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
      (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l p' g).hom)
    ((abelianPullForget k₀ l (p' ≫ g)).inv)
    (Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
      (ProEtale.adicUpperStarCongr l hw).hom)
    ((abelianPullForget k₀ l (v ≫ p)).inv)
    (Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
      (adicUpperStarGeometricFiberMapCompIso (k₀ := k₀) l v p).inv)
    (Functor.whiskerRight (abelianPullForget k₀ l p).inv
      (ProEtale.adicUpperStar l (geometricMap k₀ v)))
    (Functor.whiskerLeft (ProEtaleWeilSheaf.upperStar k₀ l p)
      (abelianPullForget k₀ l v).inv)
    (Functor.whiskerLeft (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
      (ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm).hom)
    (abelianPullSquare_hom k₀ l sq)
    (comp_inv_forget_nat k₀ l p' g)
    (congr_forget_nat k₀ l sq.w.symm hw)
    (comp_hom_forget_nat k₀ l v p)
    (geometric_pullSquare_nat k₀ l sq hw)

/-- The canonical native mate on the entire ordinary derived category. -/
def mate (sq : CommSq v p' p g) :
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory ⟶
      (ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor :=
  (mateEquiv
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p))
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p'))
    (TwoSquare.mk _ _ _ _ (pullSquare k₀ l sq).hom))

/-- The exact pullback forgetting comparison, localized from the actual carrier square. -/
def pullForget {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategory ⋙ forget k₀ l X ≅
      forget k₀ l Y ⋙ (ProEtale.adicUpperStar l (geometricMap k₀ f)).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso
    (IsoAlgebra.mapOfNatIsoCompForgetIso
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l f
        (comp_over f (Spec (CommRingCat.of k₀)))))

private theorem pullForget_eq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] :
    pullForget k₀ l f = Functor.mapDerivedCategorySquareIso (abelianPullForget k₀ l f) := by
  unfold pullForget abelianPullForget
  rfl

/-- The direct-image forgetting comparison, normalized on the common K-injective model. -/
def pushForget {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor ⋙ forget k₀ l Y ≅
      forget k₀ l X ⋙ (ProEtale.adicLowerStar l (geometricMap k₀ f)).rightDerivedFunctor := by
  letI := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  letI := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  exact IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso
    (WeilSheaf.frobeniusPullback k₀ l X)
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l f
      (comp_over f (Spec (CommRingCat.of k₀))))

private theorem pushForget_mate {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] :
    (mateEquiv
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f))
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f)))
      (TwoSquare.mk _ _ _ _ (pullForget k₀ l f).inv)) =
        (pushForget k₀ l f).hom := by
  let := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  apply Adjunction.derived_exact_forget_mate
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f)
    (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))
    (IsoAlgebra.mapOfNatIsoCompForgetIso
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l f
        (comp_over f (Spec (CommRingCat.of k₀)))))
    (IsoAlgebra.mapOfNatIsoCompForgetIso
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l f
        (comp_over f (Spec (CommRingCat.of k₀)))))
  apply NatTrans.ext
  funext M
  apply ((ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f)).homEquiv
    _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change _ = (ProEtale.adicUpperStar l (geometricMap k₀ f)).map (𝟙 _) ≫ _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hc := mateEquiv_counit
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l f)
    (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f))
    (TwoSquare.mk _ _ _ _ (IsoAlgebra.mapOfNatIsoCompForgetIso
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l f
        (comp_over f (Spec (CommRingCat.of k₀))))).inv) M
  change _ = 𝟙 _ ≫
    (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ f)).counit.app
      M.carrier at hc
  erw [Category.id_comp] at hc
  exact hc

/-- The source comparison assembled from the canonical pullback and pushforward comparisons. -/
def sourceComparison (p : Z ⟶ T) (g : T' ⟶ T)
    [p.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))] :
    ((ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory) ⋙ forget k₀ l T' ≅
      forget k₀ l Z ⋙ (ProEtale.adicLowerStar l (geometricMap k₀ p)).rightDerivedFunctor ⋙
        (ProEtale.adicUpperStar l (geometricMap k₀ g)).mapDerivedCategory :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pullForget k₀ l g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pushForget k₀ l p) _ ≪≫
    Functor.associator _ _ _

/-- The target comparison assembled from the canonical pullback and pushforward comparisons. -/
def targetComparison (v : Z' ⟶ Z) (p' : Z' ⟶ T')
    [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))] :
    ((ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor) ⋙ forget k₀ l T' ≅
      forget k₀ l Z ⋙ (ProEtale.adicUpperStar l (geometricMap k₀ v)).mapDerivedCategory ⋙
        (ProEtale.adicLowerStar l (geometricMap k₀ p')).rightDerivedFunctor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pushForget k₀ l p') ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullForget k₀ l v) _ ≪≫
    Functor.associator _ _ _

section ExactCube

open CategoryTheory.Limits

variable {C : Type*} {D : Type*} {E : Type*} {F : Type*}
variable {G : Type*} {H : Type*} {I : Type*} {J : Type*}
  [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  [Category E] [Abelian E] [HasDerivedCategory E]
  [Category F] [Abelian F] [HasDerivedCategory F]
  [Category G] [Abelian G] [HasDerivedCategory G]
  [Category H] [Abelian H] [HasDerivedCategory H]
  [Category I] [Abelian I] [HasDerivedCategory I]
  [Category J] [Abelian J] [HasDerivedCategory J]
  (a₁ : C ⥤ D)
  (b₁ : D ⥤ E)
  (c₁ : E ⥤ F)
  (d₁ : C ⥤ G)
  (e₁ : G ⥤ E)
  (f₁ : G ⥤ H)
  (g₁ : H ⥤ F)
  (h₁ : C ⥤ I)
  (i₁ : I ⥤ H)
  (j₁ : D ⥤ J)
  (k₁ : J ⥤ F)
  (m₁ : I ⥤ J)
  [a₁.Additive] [PreservesFiniteLimits a₁] [PreservesFiniteColimits a₁]
  [b₁.Additive] [PreservesFiniteLimits b₁] [PreservesFiniteColimits b₁]
  [c₁.Additive] [PreservesFiniteLimits c₁] [PreservesFiniteColimits c₁]
  [d₁.Additive] [PreservesFiniteLimits d₁] [PreservesFiniteColimits d₁]
  [e₁.Additive] [PreservesFiniteLimits e₁] [PreservesFiniteColimits e₁]
  [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [g₁.Additive] [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [h₁.Additive] [PreservesFiniteLimits h₁] [PreservesFiniteColimits h₁]
  [i₁.Additive] [PreservesFiniteLimits i₁] [PreservesFiniteColimits i₁]
  [j₁.Additive] [PreservesFiniteLimits j₁] [PreservesFiniteColimits j₁]
  [k₁.Additive] [PreservesFiniteLimits k₁] [PreservesFiniteColimits k₁]
  [m₁.Additive] [PreservesFiniteLimits m₁] [PreservesFiniteColimits m₁]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exact_inverse_cube
    (q1 : d₁ ⋙ e₁ ≅ a₁ ⋙ b₁)
    (q2 : f₁ ⋙ g₁ ≅ e₁ ⋙ c₁)
    (q3 : d₁ ⋙ f₁ ≅ h₁ ⋙ i₁)
    (q4 : b₁ ⋙ c₁ ≅ j₁ ⋙ k₁)
    (q5 : h₁ ⋙ m₁ ≅ a₁ ⋙ j₁)
    (q6 : i₁ ⋙ g₁ ≅ m₁ ⋙ k₁)
    (comm : Functor.whiskerRight q1.inv c₁ ≫
        Functor.whiskerLeft d₁ q2.inv ≫ Functor.whiskerRight q3.hom g₁ =
      Functor.whiskerLeft a₁ q4.hom ≫
        Functor.whiskerRight q5.inv k₁ ≫ Functor.whiskerLeft h₁ q6.inv) :
    ∀ X : _root_.DerivedCategory C,
      c₁.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q1).inv.app X) ≫
        (Functor.mapDerivedCategorySquareIso q2).inv.app (d₁.mapDerivedCategory.obj X) ≫
        g₁.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q3).hom.app X) =
      (Functor.mapDerivedCategorySquareIso q4).hom.app (a₁.mapDerivedCategory.obj X) ≫
        k₁.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q5).inv.app X) ≫
        (Functor.mapDerivedCategorySquareIso q6).inv.app (h₁.mapDerivedCategory.obj X) := by
  have hh := Functor.mapDerivedCategory_exactCube a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ i₁ j₁ k₁ m₁
    q1.symm q2.symm q3 q4 q5.symm q6.symm (fun X ↦ by
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Iso.symm_hom, Functor.comp_obj] using congr_app comm X)
  intro X
  simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.mapDerivedCategoryNatIso_symm, Category.assoc] using
      congr_app hh X

end ExactCube

private theorem localized_pull_cube (sq : CommSq v p' p g) :
  ∀ X : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l T),
    (ProEtale.adicUpperStar l (geometricMap k₀ p')).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (abelianPullForget k₀ l g)).inv.app X) ≫
      (Functor.mapDerivedCategorySquareIso (abelianPullForget k₀ l p')).inv.app
        ((ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory.obj X) ≫
      (forget k₀ l Z').map
        ((Functor.mapDerivedCategorySquareIso (abelianPullSquare k₀ l sq)).hom.app X) =
    (Functor.mapDerivedCategorySquareIso
      (ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm)).hom.app
        ((forget k₀ l T).obj X) ≫
      (ProEtale.adicUpperStar l (geometricMap k₀ v)).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (abelianPullForget k₀ l p)).inv.app X) ≫
      (Functor.mapDerivedCategorySquareIso (abelianPullForget k₀ l v)).inv.app
        ((ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory.obj X) := by
  have h := exact_inverse_cube
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T))
    (ProEtale.adicUpperStar l (geometricMap k₀ g))
    (ProEtale.adicUpperStar l (geometricMap k₀ p'))
    (ProEtaleWeilSheaf.upperStar k₀ l g)
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l T'))
    (ProEtaleWeilSheaf.upperStar k₀ l p')
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z'))
    (ProEtaleWeilSheaf.upperStar k₀ l p)
    (ProEtaleWeilSheaf.upperStar k₀ l v)
    (ProEtale.adicUpperStar l (geometricMap k₀ p))
    (ProEtale.adicUpperStar l (geometricMap k₀ v))
    (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
    (abelianPullForget k₀ l g) (abelianPullForget k₀ l p')
    (abelianPullSquare k₀ l sq)
    (ProEtale.adicUpperStarCompIso l (geometricSquare k₀ sq).w.symm)
    (abelianPullForget k₀ l p) (abelianPullForget k₀ l v)
    (abelianPullSquare_cube_nat k₀ l sq)
  with_reducible exact h

private theorem pullForget_cube (sq : CommSq v p' p g) :
  ∀ X : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l T),
    (ProEtale.adicUpperStar l (geometricMap k₀ p')).mapDerivedCategory.map
        ((pullForget k₀ l g).inv.app X) ≫
      (pullForget k₀ l p').inv.app
        ((ProEtaleWeilSheaf.upperStar k₀ l g).mapDerivedCategory.obj X) ≫
      (forget k₀ l Z').map ((pullSquare k₀ l sq).hom.app X) =
    (ProEtale.adicDerivedPullSquare l (geometricSquare k₀ sq)).hom.app
        ((forget k₀ l T).obj X) ≫
      (ProEtale.adicUpperStar l (geometricMap k₀ v)).mapDerivedCategory.map
        ((pullForget k₀ l p).inv.app X) ≫
      (pullForget k₀ l v).inv.app
        ((ProEtaleWeilSheaf.upperStar k₀ l p).mapDerivedCategory.obj X) := by
  simpa only [pullForget_eq, pullSquare_eq, geometricDerivedSquare_eq k₀ l sq,
    forget] using
    localized_pull_cube k₀ l sq

/-- Forgetting the native mate gives the specified geometric mate, with canonical comparisons. -/
theorem forget_mate (sq : CommSq v p' p g)
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l Z)) :
    (forget k₀ l T').map ((mate k₀ l sq).app K) =
      (sourceComparison k₀ l p g).hom.app K ≫
        (ProEtale.adicDerivedBaseChange l (geometricSquare k₀ sq)).app
          ((forget k₀ l Z).obj K) ≫
        (targetComparison k₀ l v p').inv.app K := by
  have hF : (mateEquiv
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p))
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ p)))
      (TwoSquare.mk _ _ _ _ (pullForget k₀ l p).inv)) =
        (pushForget k₀ l p).hom := pushForget_mate k₀ l p
  have hK : (mateEquiv
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p'))
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ p')))
      (TwoSquare.mk _ _ _ _ (pullForget k₀ l p').inv)) =
        (pushForget k₀ l p').hom := pushForget_mate k₀ l p'
  have hc := pullForget_cube k₀ l sq
  have h := exchangeMate_cube
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p))
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l p'))
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ p)))
    (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (ProEtale.adicUpperStarLowerStarAdjunction l (geometricMap k₀ p')))
    (forget k₀ l T) (forget k₀ l Z) (forget k₀ l T') (forget k₀ l Z')
    (pullForget k₀ l p) (pullForget k₀ l g) (pullForget k₀ l v) (pullForget k₀ l p')
    (pullSquare k₀ l sq).hom
    (ProEtale.adicDerivedPullSquare l (geometricSquare k₀ sq)).hom hc K
  change (forget k₀ l T').map ((mate k₀ l sq).app K) ≫
      (mateEquiv _ _ (TwoSquare.mk _ _ _ _ (pullForget k₀ l p').inv)).app
        ((ProEtaleWeilSheaf.upperStar k₀ l v).mapDerivedCategory.obj K) ≫
      (ProEtale.adicLowerStar l (geometricMap k₀ p')).rightDerivedFunctor.map
        ((pullForget k₀ l v).hom.app K) =
    (pullForget k₀ l g).hom.app
        ((ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor.obj K) ≫
      (ProEtale.adicUpperStar l (geometricMap k₀ g)).mapDerivedCategory.map
        ((mateEquiv _ _ (TwoSquare.mk _ _ _ _ (pullForget k₀ l p).inv)).app K) ≫
      (ProEtale.adicDerivedBaseChange l (geometricSquare k₀ sq)).app
        ((forget k₀ l Z).obj K) at h
  rw [hF, hK] at h
  rw [← cancel_mono ((targetComparison k₀ l v p').hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  simpa only [sourceComparison, targetComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
    Iso.inv_hom_id_app] using h

end AlgebraicGeometry.NativeBaseChange
