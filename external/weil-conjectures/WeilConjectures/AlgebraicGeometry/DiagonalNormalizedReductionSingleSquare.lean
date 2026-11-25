/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalReductionSingleSquare
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Natural transport of a normalized reduction on supported endpoints -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
attribute [local implicit_reducible] HomotopyCategory.singleFunctors
private theorem singleCounit_naturality
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (l : ℕ) (L : A ⥤ B) (D : DiagonalDerivedReduction l L)
    {M N : A} (h : M ⟶ N) :
    D.T.map ((DerivedCategory.singleFunctor A 0).map h) ≫
        diagonalDerivedSingleCounit l L D N =
      diagonalDerivedSingleCounit l L D M ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).map (D.ordinary.E.map h) := by
  let α : DerivedCategory.singleFunctor A 0 ⋙ D.T ⟶
      D.ordinary.E ⋙ DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0 :=
    Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQ A 0).hom D.T ≫
      Functor.whiskerLeft (CochainComplex.singleFunctor A 0) D.ε ≫
      Functor.whiskerRight (D.ordinary.E.mapCochainComplexSingleFunctor 0).hom
        DerivedCategory.Q ≫
      Functor.whiskerLeft D.ordinary.E
        (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv
  simpa only [α, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, diagonalDerivedSingleCounit] using!
      α.naturality h

/-- A normalized single reduction square commutes after any ordinary endpoint map.

Source: blueprint latest, diagonal coefficient changes (3), naturality of reduction
on the supported integral source.
(blueprint: lem-diagonal-normalized-reduction-single-square).

Proof: replace both endpoint isomorphisms by their normalized derived single counits.
Apply the single reduction square, postcomposing with the single of the primed
ordinary reduction of the endpoint map. Naturality of the derived single counit
moves this map to the primed derived reduction. Functoriality and associativity
identify the result with the reduced geometric endpoint. -/
theorem diagonalReduction_normalized_single_square
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
          K'.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (M' : C) (b : F.obj M ⟶ M')
    (a : K.T.obj ((DerivedCategory.singleFunctor A 0).obj M) ≅
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (K.ordinary.E.obj M))
    (a' : K'.T.obj ((DerivedCategory.singleFunctor C 0).obj M') ≅
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).obj (K'.ordinary.E.obj M'))
    (ha : a.hom = diagonalDerivedSingleCounit l L K M)
    (ha' : a'.hom = diagonalDerivedSingleCounit l L' K' M') :
    let V := (Functor.whiskeringRight ℕᵒᵖ B D).obj G
    V.mapDerivedCategory.map a.hom ≫
        (V.mapDerivedCategorySingleFunctor 0).hom.app (K.ordinary.E.obj M) ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map
          (e.hom.app M ≫ K'.ordinary.E.map b) =
      (q.hom.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        K'.T.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
          (DerivedCategory.singleFunctor C 0).map b)) ≫ a'.hom := by
  dsimp only
  rw [ha, ha']
  have h := diagonalReduction_single_square l L L' F G K K' e q M hn
  dsimp only at h
  have hn' := singleCounit_naturality l L' K' b
  have hp := congrArg (fun t ↦ t ≫
    (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ D) 0).map (K'.ordinary.E.map b)) h
  simp only [Category.assoc] at hp
  rw [← hn'] at hp
  simpa only [Functor.map_comp, Category.assoc] using hp

end AlgebraicGeometry.ProEtale
