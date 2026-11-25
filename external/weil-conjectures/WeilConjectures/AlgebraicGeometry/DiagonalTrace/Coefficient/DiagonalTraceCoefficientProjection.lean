/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Coefficient projections of the normalized ordinary-to-derived limit map

Source: diagonal tower trace proof, ordinary coefficient cones in steps 5--7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategorySingleFunctor

private theorem ordinaryRlim_projection
    {A : Type*} [Category A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (H : ℕᵒᵖ ⥤ A) (n : ℕ) :
    diagonalOrdinaryRlim L H ≫ (L.projection n).app _ ≫
        (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app H =
      (DerivedCategory.singleFunctor A 0).map (limit.π H (op n)) := by
  let E := (evaluation ℕᵒᵖ A).obj (op n)
  let P := (HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0).obj H
  have hn := L.normalization P n
  simp only [diagonalOrdinaryRlim, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  erw [L.R.map_id, Category.comp_id]
  rw [E.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  simp only [← DerivedCategory.Q.map_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self, P, E,
      Category.assoc]
  · simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, HomologicalComplex.single, hi]

private theorem cone_comparison
    {C D : Type*} [Category C] [Category D] (L E : C ⥤ D) (π : L ⟶ E)
    {X Y : C} (e : X ≅ Y) {I J K Z : D}
    (a : I ⟶ J) (b : J ⟶ K) (c : K ⟶ L.obj Y) (d : E.obj Y ⟶ Z)
    (r : K ⟶ Z) (q : J ⟶ Z)
    (hn : c ≫ π.app Y ≫ d = r) (hq : b ≫ r = q) :
    a ≫ b ≫ c ≫ L.map e.inv ≫ π.app X ≫ E.map e.hom ≫ d = a ≫ q := by
  rw [π.naturality_assoc, ← E.map_comp_assoc, e.inv_hom_id,
    E.map_id, Category.id_comp, hn, hq]

/-- Evaluating the normalized derived-limit comparison of an ordinary cone gives
its actual ordinary projection under the canonical single-object comparisons.

Source: diagonal tower trace proof steps 5--7
(blueprint: lem-sfb-diagonal-trace-exact-cone-projection).
Proof: normalize the derived-limit projection on the single complex of the tower.
Naturality moves the inverse restriction/single comparison across that projection;
its inverse cancels the forward comparison. The normalized ordinary-limit arrow
then becomes the single of the ordinary limit projection. Functoriality and the
ordinary cone lift equation give the specified component of the input cone. -/
theorem diagonalTrace_exactConeComparison_projection
    {A : Type*} {B : Type*} {C : Type*}
    [Category A] [Category B] [Category C] [Abelian A] [Abelian B] [Abelian C]
    [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory C]
    (U : A ⥤ B) (V : C ⥤ (ℕᵒᵖ ⥤ B)) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim B) (M : A) (N : C)
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N) (n : ℕ) :
    exactConeComparison U V L M N π ≫ (L.projection n).app _ ≫
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map
          ((V.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app _ =
      (U.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map (π.app (op n)) := by
  let E := (evaluation ℕᵒᵖ B).obj (op n)
  let S := DerivedCategory.singleFunctor B 0
  let b := S.map (limit.lift (V.obj N) ⟨U.obj M, π⟩)
  have hq : b ≫ S.map (limit.π (V.obj N) (op n)) = S.map (π.app (op n)) := by
    dsimp only [b]
    rw [← S.map_comp, limit.lift_π]
  unfold exactConeComparison
  simp only [Category.assoc]
  exact cone_comparison L.R E.mapDerivedCategory (L.projection n)
    ((V.mapDerivedCategorySingleFunctor 0).app N)
    ((U.mapDerivedCategorySingleFunctor 0).hom.app M) b
    (diagonalOrdinaryRlim L (V.obj N))
    ((E.mapDerivedCategorySingleFunctor 0).hom.app (V.obj N))
    (S.map (limit.π (V.obj N) (op n))) (S.map (π.app (op n)))
    (ordinaryRlim_projection L (V.obj N) n) hq

end AlgebraicGeometry.ProEtale.DiagonalTrace
