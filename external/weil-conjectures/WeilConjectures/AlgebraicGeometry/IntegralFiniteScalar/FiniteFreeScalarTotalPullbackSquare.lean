/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
/-! # A tensor square from its degree-zero coefficient summands
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
/-- A total tensor comparison commutes with an oplax functor whenever the
coefficient square commutes on its invertible degree-zero summands. -/
theorem finiteFreeScalar_totalPullbackSquare
    {A B : Type*} [Category.{u + 1} A] [Category.{u + 1} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [MonoidalClosed A] [MonoidalClosed B] [BraidedCategory A] [BraidedCategory B]
    (F : A ⥤ B) [F.Additive] [F.IsLeftAdjoint] [F.OplaxMonoidal]
    (P K U : CochainComplex A ℤ) (PX V : CochainComplex B ℤ)
    (τY : P ⊗ K ≅ U)
    (τX : PX ⊗ (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ V)
    (p : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ PX)
    (q : (F.mapHomologicalComplex (.up ℤ)).obj U ⟶ V)
    (RY : A) (RX : B) (tY : P.X 0 ⟶ RY) (tX : PX.X 0 ⟶ RX)
    (r : F.obj RY ⟶ RX)
    (κY : ∀ n, RY ⊗ K.X n ⟶ U.X n)
    (κX : ∀ n, RX ⊗ F.obj (K.X n) ⟶ V.X n)
    [IsIso tY] [∀ n, IsIso (κY n)]
    (hY : ∀ n, HomologicalComplex.ιTensorObj P K 0 n n (zero_add n) ≫
      τY.hom.f n = tY ▷ K.X n ≫ κY n)
    (hX : ∀ n, HomologicalComplex.ιTensorObj PX
        ((F.mapHomologicalComplex (.up ℤ)).obj K) 0 n n (zero_add n) ≫
      τX.f n = tX ▷ F.obj (K.X n) ≫ κX n)
    (ho : ∀ n, F.map (κY n) ≫ q.f n =
      Functor.OplaxMonoidal.δ F RY (K.X n) ≫ r ▷ F.obj (K.X n) ≫ κX n)
    (ht : F.map tY ≫ r = p.f 0 ≫ tX) :
    (F.mapHomologicalComplex (.up ℤ)).map τY.hom ≫ q =
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app K ≫
        HomologicalComplex.tensorHom p (𝟙 _) ≫ τX := by
  ext n : 1
  let i := HomologicalComplex.ιTensorObj P K 0 n n (zero_add n)
  have hi : IsIso (i ≫ τY.hom.f n) := by
    dsimp only [i]
    rw [hY]
    infer_instance
  have : IsIso i := IsIso.of_isIso_comp_right i (τY.hom.f n)
  apply (cancel_epi (F.map i)).1
  have hs : F.map i ≫
      (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app K).f n =
    Functor.OplaxMonoidal.δ F (P.X 0) (K.X n) ≫
      HomologicalComplex.ιTensorObj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj K) 0 n n (zero_add n) := by
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P K 0 n n (zero_add n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [← F.map_comp_assoc, hY, F.map_comp]
  erw [reassoc_of% hs, HomologicalComplex.ι_mapBifunctorMap_assoc, hX]
  simp only [HomologicalComplex.id_f, Category.assoc]
  change F.map (tY ▷ K.X n) ≫ (F.map (κY n) ≫ q.f n) =
    Functor.OplaxMonoidal.δ F (P.X 0) (K.X n) ≫
      (p.f 0 ▷ F.obj (K.X n)) ≫ (PX.X 0 ◁ 𝟙 _) ≫
        (tX ▷ F.obj (K.X n)) ≫ κX n
  simp only [whiskerLeft_id, Category.id_comp]
  erw [ho n]
  erw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ht]
end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
