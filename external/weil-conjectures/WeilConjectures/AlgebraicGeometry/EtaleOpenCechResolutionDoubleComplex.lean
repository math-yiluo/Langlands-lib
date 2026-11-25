/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.AlgebraicGeometry.Sites.Small
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-! # The Čech double complex on opens with large étale coefficients

Source: Stacks Project, Tag 03AZ, construction from an injective resolution.
(blueprint: def-sc-etale-open-cech-resolution-double-complex)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The Čech functor preserves zero morphisms, also for larger coefficients.
Source: the degree maps are products of zero morphisms.
(blueprint: def-sc-etale-open-cech-resolution-double-complex) -/
instance etaleOpenCech_preservesZeroMorphisms (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) :
    (cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U).PreservesZeroMorphisms where
  map_zero := by
    intro P Q
    apply HomologicalComplex.hom_ext
    intro n
    dsimp [cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor,
      AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.map, Limits.FormalCoproduct.evalOp]
    apply Pi.hom_ext
    intro t
    simp

/-- Apply the open Čech complex functor to each term of the actual injective
resolution, and flip the indices to put the Čech degree first.
Source: Stacks Project, Tag 03AZ.
(blueprint: def-sc-etale-open-cech-resolution-double-complex) -/
noncomputable def etaleOpenCechResolutionDoubleComplex
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    {ι : Type u} (U : ι → X.Opens)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution G) :
    HomologicalComplex₂ AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.flip
    (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj i.op ⋙
        cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)

end AlgebraicGeometry.Scheme
