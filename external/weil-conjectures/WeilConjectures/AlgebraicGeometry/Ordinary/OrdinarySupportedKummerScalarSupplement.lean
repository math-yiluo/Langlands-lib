/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalar

/-!
# Derived coefficient change of supported Kummer classes

## Main definitions

* `SupportedDerivedScalarUnit`: the derived scalar-unit universal property.
* `SupportedKummerScalar`: the normalized scalar-extension square for the classes.

## References

* Stacks 07A6
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

/-- The scalar-extension clause, with the comparison maps fixed on generators.
Both displayed universal properties refer to the canonical sectionwise scalar maps:
constants send r to φ(r), roots send a ⊗ z to φ(a) ⊗ z. The Ext square is the assertion
that the class itself is obtained by the same derived scalar extension. -/
@[irreducible]
def SupportedKummerScalar {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T)
    (cR : Ext ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      (Scheme.finiteEtaleTateLine T N R hR) 2)
    (cS : Ext ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      (Scheme.finiteEtaleTateLine T N S hS) 2) : Prop :=
  ∃ (η : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
    (θ : Scheme.finiteEtaleTateLine T N R hR ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj
        (Scheme.finiteEtaleTateLine T N S hS)),
    (∀ (U : D.Etaleᵒᵖ) (r : R),
      η.hom.app U
        ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r)) ∧
    (∀ (U : T.Etaleᵒᵖ) (r : R) (z : (T.rootsOfUnitySheaf N).obj.obj U),
      θ.hom.app U (Scheme.finiteEtaleTateOneGenerator R N T hR U r z) =
        Scheme.finiteEtaleTateOneGenerator S N T hS U (φ r) z) ∧
    SupportedDerivedScalarUnit φ T
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (ordinaryFiniteConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    SupportedDerivedScalarUnit φ T (Scheme.finiteEtaleTateLine T N R hR)
      (Scheme.finiteEtaleTateLine T N S hS) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars T.smallEtaleTopology φ)) (zero_add 2) =
      cR.comp (Ext.mk₀ θ) (add_zero 2)

end AlgebraicGeometry.Etale
