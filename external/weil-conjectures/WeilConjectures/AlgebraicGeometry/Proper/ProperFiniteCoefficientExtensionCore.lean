/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit

/-! # Proper finite coefficient extension core

The isomorphism and restriction/projection clauses of proper finite coefficient extension
(the mate normalization clause is added separately).

## Implementation details

The proof chooses K-flat resolutions with flat terms, identifies scalar, tensor, pullback and
direct-image comparisons termwise, and applies the proper projection formula after exact
conservative restriction of scalars. The resulting restricted morphism is invertible, so
conservativity gives invertibility of the scalar mate; the same calculation gives the ordered
projection identity. The construction descends through quasi-isomorphisms to the entire
derived category.

## References

* Stacks Project, Tag 0GL6
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem cancel_scalar_comparisons
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M N P O : D} {S T U V : C}
    (e : M ≅ N) (d : U ≅ T) (p : N ⟶ F.obj S) (c : S ⟶ T)
    (m : M ⟶ P) (n : P ⟶ F.obj U) (s : O ⟶ N) (k : T ⟶ V)
    (h : m ≫ n = e.hom ≫ p ≫ F.map (c ≫ d.inv)) :
    s ≫ e.inv ≫ m ≫ n ≫ F.map (d.hom ≫ k) = s ≫ p ≫ F.map (c ≫ k) := by
  simp only [Functor.map_comp] at h ⊢
  rw [reassoc_of% h]
  simp [← Functor.map_comp]

/-- For proper `f` between Noetherian schemes, the scalar mate is an isomorphism on the unbounded
derived category, and after restriction of scalars it agrees with the projection formula
comparison. -/
theorem properFiniteCoefficientExtensionCore
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsNoetherian X] [IsNoetherian Y] :
    (∀ L : DerivedCategoryModule R X,
      IsIso ((scalarMate φ f).app L)) ∧
    (∀ L : DerivedCategoryModule R X,
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (scalarTensorIso φ Y).inv.app
          (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
          ((scalarMate φ f).app L) ≫
        (scalarRestrictionDirectImageMap φ f).app
          ((scalarExtension φ X).obj L) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          ((scalarTensorIso φ X).hom.app L ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X)) =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) f).app L).app
          (scalarCoefficient φ Y) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).map
              ((scalarCoefficientPullbackIso φ f).hom) ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X))):= by
  constructor
  · exact fun L ↦ proper_scalarMate_isIso φ f L
  · intro L
    exact cancel_scalar_comparisons
      R((f)_*[ModuleCat.{u + 1} R])
      ((scalarTensorIso φ Y).app (R((f)_*[ModuleCat.{u + 1} R]).obj L))
      ((scalarTensorIso φ X).app L) _ _ _ _ _ _
      (scalar_projection_ambient φ f L)

end AlgebraicGeometry.Etale
