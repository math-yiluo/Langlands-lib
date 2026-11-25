/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore

/-! # Transposition through finite realization

Source: the exact functor single comparisons and adjunction triangle identities.
(blueprint: lem-diagonal-realized-endpoint-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local irreducible] Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive
open RootEndpointTranspose RootEndpointTranspose.ShiftHelpers

private theorem shifted_composition
    {C D K : Type*} [Category C] [Category D] [Category K]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift K ℤ]
    (F : C ⥤ D) (G : D ⥤ K) [F.CommShift ℤ] [G.CommShift ℤ]
    {M : C} {N : D} {P : K} (f : F.obj M ⟶ N) (g : G.obj N ⟶ P) (k : ℤ) :
    G.map ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') ≫
        (G.commShiftIso k).hom.app N ≫ g⟦k⟧' =
      ((F ⋙ G).commShiftIso k).hom.app M ≫ (G.map f ≫ g)⟦k⟧' := by
  simp only [Functor.map_comp, Functor.commShiftIso_comp_hom_app,
    (shiftFunctor K k).map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]

/-- An already normalized endpoint remains normalized after finite realization.
Source: diagonal tower coefficient changes (1), finite realization
(blueprint: lem-diagonal-realized-endpoint-transpose).
Proof: compose the supplied normalization with the finite equivalence transpose.
Exact-single composition coherence collects the two restrictions into one right
functor, while the ordinary equivalence unit defines the root insertion. -/
theorem realizedEndpoint_transpose
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization Λ B X)
    (R : Modules Λ X ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {F : DerivedCategory C ⥤ DerivedCategory (Modules Λ X)}
    (a : F ⊣ R.mapDerivedCategory)
    {M : C} {N : Modules Λ X}
    {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)}
    (f : F.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N)
    (v : M ⟶ R.obj N)
    (hf : a.homEquiv _ _ f = (DerivedCategory.singleFunctor C 0).map v ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N)
    (i : e.F.obj N ≅ P) :
    ((a.comp (UniformizerSquareData.finiteAdjunction e)).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse R)).homEquiv _ _
      (e.F.mapDerivedCategory.map f ≫
        (e.F.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor _ 0).map i.hom) =
      (DerivedCategory.singleFunctor C 0).map (v ≫ R.map (e.rootInsertion N i)) ≫
        ((e.F.asEquivalence.inverse ⋙ R).mapDerivedCategorySingleFunctor 0).inv.app P := by
  exact composite_single_transpose R e.F.asEquivalence.inverse a
    (UniformizerSquareData.finiteAdjunction e) f
    ((e.F.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor _ 0).map i.hom)
    v (e.rootInsertion N i) hf (finiteEndpoint_transpose e N i)

/-- Finite realization carries a shifted endpoint to the shifted realized endpoint.
Source: diagonal tower coefficient changes (1), exact shift comparisons
(blueprint: lem-diagonal-realized-endpoint-transpose).
Proof: unfold the finite target map. Shift naturality moves the scalar endpoint
through realization, and the composite shift comparison collects the two factors. -/
theorem realizedEndpoint_shift
    {C : Type*} [Category C] [HasShift C ℤ]
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization Λ B X)
    (F : C ⥤ DerivedCategory (Modules Λ X)) [F.CommShift ℤ]
    {M : C} {N : Modules Λ X}
    {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)}
    (f : F.obj M ⟶ (DerivedCategory.singleFunctor _ 0).obj N) (i : e.F.obj N ≅ P) :
    finiteTargetMap e ((F.commShiftIso (2 : ℤ)).hom.app M ≫ f⟦(2 : ℤ)⟧') i =
      ((F ⋙ e.F.mapDerivedCategory).commShiftIso (2 : ℤ)).hom.app M ≫
        (e.F.mapDerivedCategory.map f ≫
          (e.F.mapDerivedCategorySingleFunctor 0).hom.app N ≫
            (DerivedCategory.singleFunctor _ 0).map i.hom)⟦(2 : ℤ)⟧' := by
  unfold finiteTargetMap
  exact shifted_composition F e.F.mapDerivedCategory f
    ((e.F.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor _ 0).map i.hom) (2 : ℤ)

/-- Prescribing the ordinary insertion determines the realized endpoint transpose.
Source: diagonal tower coefficient changes (1), normalized root insertions
(blueprint: lem-diagonal-realized-endpoint-transpose).
Proof: apply finite realization transposition and substitute the supplied ordinary
insertion identity under the exact single functor. -/
theorem realizedEndpoint_transpose_eq
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization Λ B X)
    (R : Modules Λ X ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {F : DerivedCategory C ⥤ DerivedCategory (Modules Λ X)}
    (a : F ⊣ R.mapDerivedCategory)
    {M : C} {N : Modules Λ X}
    {P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)}
    (f : F.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N)
    (v : M ⟶ R.obj N)
    (hf : a.homEquiv _ _ f = (DerivedCategory.singleFunctor C 0).map v ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N)
    (i : e.F.obj N ≅ P)
    (w : M ⟶ (e.F.asEquivalence.inverse ⋙ R).obj P)
    (hw : v ≫ R.map (e.rootInsertion N i) = w) :
    ((a.comp (UniformizerSquareData.finiteAdjunction e)).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse R)).homEquiv _ _
      (e.F.mapDerivedCategory.map f ≫
        (e.F.mapDerivedCategorySingleFunctor 0).hom.app N ≫
          (DerivedCategory.singleFunctor _ 0).map i.hom) =
      (DerivedCategory.singleFunctor C 0).map w ≫
        ((e.F.asEquivalence.inverse ⋙ R).mapDerivedCategorySingleFunctor 0).inv.app P := by
  exact (realizedEndpoint_transpose e R a f v hf i).trans
    (congrArg (fun z ↦ (DerivedCategory.singleFunctor C 0).map z ≫
      ((e.F.asEquivalence.inverse ⋙ R).mapDerivedCategorySingleFunctor 0).inv.app P) hw)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
