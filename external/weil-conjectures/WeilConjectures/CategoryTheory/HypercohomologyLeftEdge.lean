/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! # The left edge for a single bounded below complex

Source: Stacks Project, derived.tex, Tags 015J and 015N.
(blueprint: def-pc-hypercohomology-left-edge).
-/

@[expose] public section

universe uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- The truncation spectral object functor for `RG`, without an initial functor `F`.
Source: Stacks Project, Tag 015J (blueprint: def-pc-hypercohomology-left-edge). -/
noncomputable def hypercohomologySpectralObjectFunctor :
    DerivedCategory.Plus B ⥤ Abelian.SpectralObject C EInt :=
  DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
    G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
    (DerivedCategory.Plus.homologyFunctor C 0).mapHomologicalSpectralObject EInt

/-- Nonnegative complexes give first-quadrant truncation spectral objects.
Source: Stacks Project, Tag 015J (blueprint: def-pc-hypercohomology-left-edge). -/
instance (K : DerivedCategory.Plus B) [DerivedCategory.Plus.TStructure.t.IsGE K 0] :
    (G.hypercohomologySpectralObjectFunctor.obj K).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    have := t.isZero_eTruncLT_obj_obj K 0 j hj
    change IsZero (((DerivedCategory.Plus.homologyFunctor C 0).shift n).obj
      (G.rightDerivedFunctorPlus.obj ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K))))
    exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ this))
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    have := t.isGE_eTruncGE_obj_obj (n + 1) i (by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i => simp at hi ⊢; omega
      | top => simp) ((t.eTruncLT.obj j).obj K)
    exact G.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K)) (n + 1) (by omega)

/-- The canonical identification of the left-edge target with `G Hⁿ`.
All factors are the natural truncation, shift and degree-zero comparisons.
Source: Stacks Project, Tag 015J (blueprint: def-pc-hypercohomology-left-edge). -/
noncomputable def hypercohomologyLeftEdgeTargetIso (n : ℕ) :
    G.hypercohomologySpectralObjectFunctor ⋙ Abelian.SpectralObject.hFunctor n
        (ComposableArrows.mk₁ (homOfLE
          (show ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt) by simp))) ≅
      DerivedCategory.Plus.homologyFunctor B n ⋙ G := by
  let H₀ := DerivedCategory.Plus.homologyFunctor C 0
  let RG := G.rightDerivedFunctorPlus
  let Hn := DerivedCategory.Plus.homologyFunctor B n
  exact Functor.isoWhiskerRight
      (DerivedCategory.Plus.eTruncLTCompETruncGEIso (n : ℤ)) (RG ⋙ H₀.shift (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft Hn (Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).symm
      (RG ⋙ H₀.shift (n : ℤ))) ≪≫
    Functor.isoWhiskerLeft (Hn ⋙ DerivedCategory.Plus.singleFunctor B 0)
      (Functor.isoWhiskerRight (RG.commShiftIso (-(n : ℤ))) (H₀.shift (n : ℤ))) ≪≫
    Functor.isoWhiskerLeft (Hn ⋙ DerivedCategory.Plus.singleFunctor B 0 ⋙ RG)
      (H₀.shiftIso (-(n : ℤ)) (n : ℤ) 0 (by ring)) ≪≫
    Functor.isoWhiskerLeft Hn
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0) ≪≫
    Functor.isoWhiskerLeft Hn G.rightDerivedZeroIsoSelf

/-- The unit followed by the truncation left edge, on a complex indexed by naturals.
The extension and quotient comparisons are explicit; no resolution is chosen here.
Source: Stacks Project, Tags 015J and 015N
(blueprint: def-pc-hypercohomology-left-edge). -/
noncomputable def cochainHypercohomologyLeftEdge (K : CochainComplex B ℕ) (n : ℕ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ⟶
      G.obj (K.homology n) := by
  let L : CochainComplex.Plus B :=
    ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  have : DerivedCategory.Plus.TStructure.t.IsGE (DerivedCategory.Plus.Q.obj L) 0 := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsGE 0)
  let GL := G.mapCochainComplexPlus.obj L
  let e := HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat G
  exact (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).inv ≫
    HomologicalComplex.homologyMap e.inv (n : ℤ) ≫
    (DerivedCategory.Plus.homologyFunctorObjQIso GL n).inv ≫
    (DerivedCategory.Plus.homologyFunctor C n).map
      (G.rightDerivedFunctorPlusUnit.app L) ≫
    (G.hypercohomologySpectralObjectFunctor.obj (DerivedCategory.Plus.Q.obj L)).leftEdge n ≫
    (G.hypercohomologyLeftEdgeTargetIso n).hom.app (DerivedCategory.Plus.Q.obj L) ≫
    G.map ((DerivedCategory.Plus.homologyFunctorObjQIso L n).hom ≫
      (K.extendHomologyIso ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom)

end CategoryTheory.Functor
