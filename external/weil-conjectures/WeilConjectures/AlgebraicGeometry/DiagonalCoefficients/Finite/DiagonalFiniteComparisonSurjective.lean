/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology

/-! # Lifting finite-line morphisms through the site comparison

Source: bounded-below cohomology comparison, specialized to a sheaf shifted by two.
(blueprint: lem-diagonal-finite-comparison-surjective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory HasDerivedCategory.standard
  Scheme.finiteEtaleTateLine

/-- Every arrow to the finite line shifted by two has an ordinary etale preimage.
Source: bounded-below cohomology comparison (theorem-bounded-below-cohomology-comparison).
(blueprint: lem-diagonal-finite-comparison-surjective).

Proof: the target is a sheaf in degree zero shifted by two, so it lies in degrees
at least -2. The existing comparison Hom map is bijective whenever its target
is bounded below. Apply its surjectivity to w and reverse the resulting equation.
No positivity, finiteness, or nonemptiness is required; zero rings, N=0, and the
empty scheme satisfy the same argument. -/
theorem finite_comparison_surjective
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (X : Scheme.{u})
    (w : geoP1Unit A X ⟶ geoP1Twist A N hA X 1 2) :
    ∃ k : Etale.ordinaryFiniteUnit A X ⟶ Etale.p1DecompositionTwist A N hA X 1 2,
      w = (geoP1Comparison A X).map k := by
  obtain ⟨k, hk⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map _ _
    ⟨-2, DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2)⟩).surjective w
  exact ⟨k, hk.symm⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
