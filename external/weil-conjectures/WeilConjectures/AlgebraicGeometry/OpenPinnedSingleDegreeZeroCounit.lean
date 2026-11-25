/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction
import all WeilConjectures.AlgebraicGeometry.OpenPinnedSingleTensorRestrictionFactors

/-! # Restriction of the pinned single tensor counit
Source: Stacks Project, Tags 08DW, 08IB and 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The degree-zero counit selected by the pullback composition structure.
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit). -/
def openPinnedSingleDegreeZeroCounit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) :
    (derivedPullback k).obj ((DerivedCategory.singleFunctor.{w} _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor.{w} _ 0).obj ((Scheme.Modules.tensorPullback k).obj M) :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback k) (ComplexShape.up ℤ) 0).hom.app M)))

private theorem assembleCounitSquare
    {C : Type*} [Category C] {A B C₀ D E F G H I J : C}
    (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ D) (d : D ⟶ E)
    (e : C₀ ⟶ F) (f : F ⟶ G) (g : G ⟶ H) (h : H ⟶ E)
    (i : A ⟶ I) (j : I ⟶ G) (k : I ⟶ J) (l : J ⟶ H) (s : A ⟶ J)
    (hT : c ≫ d = e ≫ f ≫ g ≫ h)
    (hc : a ≫ b ≫ e ≫ f = i ≫ j)
    (hn : k ≫ l = j ≫ g) (hR : i ≫ k = s) :
    a ≫ (b ≫ c) ≫ d = s ≫ l ≫ h := by
  calc
    a ≫ (b ≫ c) ≫ d = a ≫ b ≫ e ≫ f ≫ g ≫ h := by
      rw [Category.assoc, hT]
    _ = (a ≫ b ≫ e ≫ f) ≫ g ≫ h := by simp only [Category.assoc]
    _ = i ≫ j ≫ g ≫ h := by rw [hc, Category.assoc]
    _ = i ≫ k ≫ l ≫ h := by rw [← Category.assoc j, ← hn, Category.assoc]
    _ = s ≫ l ≫ h := by rw [← Category.assoc i, hR]

-- Nested derived and homotopy comparisons require additional typeclass reduction.
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of the pinned counit, before applying any direct image.
Source: Stacks Project, Tags 08DW, 08IB and 08HY.
(blueprint: lem-pc-open-pinned-single-degree-zero-counit).
Proof: compare the tensor pullback of a restricted module with restriction of its
pullback by the underived composition comparisons and uniqueness of open pullback
as left adjoint to pushforward. Apply the exact single-complex restriction
comparison. On K-flat representatives the pinned left-derived counit is the
localization of this underived tensor map. Its factorization equation, and the
factorization equations for the pinned composition comparisons and the constructed
open-pullback isomorphisms, identify the two paths. Thus the equality holds before
localization and descends. The source path is exactly the constructed
singleComplexRestrictedCoefficient with the identity coefficient map. Every factor is natural in M,
so the target comparisons
assemble to a natural isomorphism. The construction applies to empty opens and zero
modules, with no flatness assumption on M. -/
theorem open_pinned_single_degree_zero_counit_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k) :
    ∃ t : (Scheme.Modules.tensorPullback k ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0) ⋙
          (schemeOpenRestriction X' U').mapDerivedCategory ≅
        schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j ⋙
          DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace)) 0,
      ∀ M : X.Modules,
        let K := (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
        let H := (schemeOpenRestriction X U).obj M
        let s := ((schemeOpenRestriction X U).mapDerivedCategorySingleFunctor 0).hom.app M
        singleComplexRestrictedCoefficient k K ((derivedPullback k).obj K)
            (𝟙 _) U U' j hj ≫
          (schemeOpenRestriction X' U').mapDerivedCategory.map
            (openPinnedSingleDegreeZeroCounit k M) ≫ t.hom.app M =
          (derivedPullback j).map s ≫ openPinnedSingleDegreeZeroCounit j H := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let P := (HomotopyCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0)
  let t := openPinnedSingleTargetRestrictionIso.{u, w} k U U' j hj
  refine ⟨t, ?_⟩
  intro M
  obtain ⟨hR, hT⟩ := open_pinned_single_tensor_restriction_factors.{u, w} k U U' j hj M
  have hc := open_pinned_counit_homotopy_restriction.{u, w} k U U' j hj (P.obj M)
  let qR := (HomotopyCategory.quotient _ (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (schemeOpenRestriction X U) (.up ℤ) 0).hom.app M)
  let qj := (HomotopyCategory.quotient _ (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback j) (.up ℤ) 0).hom.app
        ((schemeOpenRestriction X U).obj M))
  have hn := (pinnedPullbackCounit.{u, w} j).naturality qR
  dsimp only [Functor.comp_map] at hn
  have hR' := (Functor.map_comp (derivedPullback j)
    ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app (P.obj M))
    (DerivedCategory.Qh.map qR)).symm.trans
      (congrArg (fun f ↦ (derivedPullback j).map f) hR)
  with_unfolding_all
    simp only [openPinnedSingleDegreeZeroCounit, cast_eq, Functor.map_comp]
    exact assembleCounitSquare _ _ _ _ _ _ _ _ _ _ _ _ _ hT hc hn hR'

end AlgebraicGeometry
