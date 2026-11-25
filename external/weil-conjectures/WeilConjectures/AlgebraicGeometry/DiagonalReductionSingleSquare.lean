/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # The single-object normalization of a reduction square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
attribute [local implicit_reducible] HomotopyCategory.singleFunctors

/-- Termwise application preserves finite limits, since it preserves each finite
limit shape pointwise. Source: Mathlib pointwise functor limits.
(blueprint: lem-diagonal-exact-whiskering). -/
instance diagonalReductionWhiskering_preservesFiniteLimits
    {B D : Type*} [Category B] [Category D] [HasFiniteLimits B]
    (G : B ⥤ D) [PreservesFiniteLimits G] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj G) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Termwise application preserves finite colimits, since it preserves each finite
colimit shape pointwise. Source: Mathlib pointwise functor colimits.
(blueprint: lem-diagonal-exact-whiskering). -/
instance diagonalReductionWhiskering_preservesFiniteColimits
    {B D : Type*} [Category B] [Category D] [HasFiniteColimits B]
    (G : B ⥤ D) [PreservesFiniteColimits G] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B D).obj G) where
  preservesFiniteColimits _ _ _ := inferInstance

-- The cochain single comparison checks several nested exact-functor constructions.
/-- A comparison of reduction counits on a single complex gives its degree-zero square.

Source: blueprint latest, diagonal coefficient changes (3), reduction of the supported
integral source.
(blueprint: lem-diagonal-reduction-single-square).

Proof: expand the two single counits and the exact inverse-image single comparison.
Use the supplied counit square on the single complex. Naturality of the second
counit moves the cochain single comparison across it; naturality of the exact
localization comparison does the same on the first side. The remaining identity
is an identity of cochain maps: in degree zero it is naturality of the ordinary
square, and in every other degree its source is zero. No isomorphism of a reduction
counit or detection by finite evaluation is needed. -/
theorem diagonalReduction_single_square
    {A B C D : Type*}
    [Category A] [Abelian A] [Category B] [Abelian B]
    [Category C] [Abelian C] [Category D] [Abelian D]
    [hA : HasDerivedCategory A] [hC : HasDerivedCategory C]
    [hBS : HasDerivedCategory (ℕᵒᵖ ⥤ B)] [hDS : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (l : ℕ) (L : A ⥤ B) (L' : C ⥤ D)
    (F : A ⥤ C) (G : B ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DiagonalDerivedReduction l L) (K' : DiagonalDerivedReduction l L')
    (e : K.ordinary.E ⋙ (Functor.whiskeringRight ℕᵒᵖ B D).obj G ≅ F ⋙ K'.ordinary.E)
    (q : K.T ⋙ ((Functor.whiskeringRight ℕᵒᵖ B D).obj G).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ K'.T) (M : A)
    (hn : let V := (Functor.whiskeringRight ℕᵒᵖ B D).obj G
      let P := (CochainComplex.singleFunctor A 0).obj M
      V.mapDerivedCategory.map (K.ε.app P) ≫
          V.mapDerivedCategoryFactors.hom.app
            ((K.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
        q.hom.app (DerivedCategory.Q.obj P) ≫
          K'.T.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          K'.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    let V := (Functor.whiskeringRight ℕᵒᵖ B D).obj G
    V.mapDerivedCategory.map (diagonalDerivedSingleCounit l L K M) ≫
        (V.mapDerivedCategorySingleFunctor 0).hom.app (K.ordinary.E.obj M) ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map (e.hom.app M) =
      q.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        K'.T.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        diagonalDerivedSingleCounit l L' K' (F.obj M) := by
  let V := (Functor.whiskeringRight ℕᵒᵖ B D).obj G
  let P := (CochainComplex.singleFunctor A 0).obj M
  have hsingle (N : C) : diagonalDerivedSingleCounit l L' K' N =
      K'.ε.app ((CochainComplex.singleFunctor C 0).obj N) ≫
        DerivedCategory.Q.map ((K'.ordinary.E.mapCochainComplexSingleFunctor 0).hom.app N) := by
    simp only [diagonalDerivedSingleCounit, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [K'.T.map_id]
    erw [Category.id_comp, Category.comp_id]
    rfl
  have hsingle' : diagonalDerivedSingleCounit l L K M =
      K.ε.app P ≫
        DerivedCategory.Q.map ((K.ordinary.E.mapCochainComplexSingleFunctor 0).hom.app M) := by
    simp only [diagonalDerivedSingleCounit, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [K.T.map_id]
    erw [Category.id_comp, Category.comp_id]
    rfl
  dsimp only
  rw [hsingle', hsingle, F.mapDerivedCategorySingleFunctor_hom_app_eq,
    V.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Functor.map_comp, Category.assoc]
  have hV := V.mapDerivedCategoryFactors.hom.naturality
    ((K.ordinary.E.mapCochainComplexSingleFunctor 0).hom.app M)
  dsimp only [Functor.comp_map] at hV
  erw [reassoc_of% hV]
  have hε := K'.ε.naturality ((F.mapCochainComplexSingleFunctor 0).hom.app M)
  dsimp only [Functor.comp_map] at hε
  erw [reassoc_of% hε]
  have hc :
      (V.mapHomologicalComplex (.up ℤ)).map
          ((K.ordinary.E.mapCochainComplexSingleFunctor 0).hom.app M) ≫
        (V.mapCochainComplexSingleFunctor 0).hom.app (K.ordinary.E.obj M) ≫
        (CochainComplex.singleFunctor (ℕᵒᵖ ⥤ D) 0).map (e.hom.app M) =
      (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P ≫
        (K'.ordinary.E.mapHomologicalComplex (.up ℤ)).map
          ((F.mapCochainComplexSingleFunctor 0).hom.app M) ≫
        (K'.ordinary.E.mapCochainComplexSingleFunctor 0).hom.app (F.obj M) := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
        HomologicalComplex.singleObjXSelf,
        HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.single, P]
    · exact (V.map_isZero (K.ordinary.E.map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi))).eq_of_src _ _
  have hmap : (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map (e.hom.app M) =
      DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (ℕᵒᵖ ⥤ D) 0).map (e.hom.app M)) := rfl
  have hc' := congrArg (fun t ↦ V.mapDerivedCategory.map (K.ε.app P) ≫
    V.mapDerivedCategoryFactors.hom.app
      ((K.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) ≫ DerivedCategory.Q.map t) hc
  simp only [Functor.map_comp] at hc'
  rw [hmap]
  erw [hc']
  erw [reassoc_of% hn]
  rfl

end AlgebraicGeometry.ProEtale
