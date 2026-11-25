/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.QuasiFiniteOverPolynomialAlgebra
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.LocalizedChart

/-!
# Quasi-finite polynomial charts

The polynomial chart produced by the affine quasi-finite theorem.

## References

* Stacks Project, Tag 00QE and its affine translation in Tag 00RH
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A prescribed natural fibre dimension yields a quasi-finite polynomial chart. -/
theorem exists_quasiFinite_polynomial_chart_data
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) (n : ℕ)
    (hdim : topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞)) :
    ∃ U : X.Opens, IsAffine U.toScheme ∧ y ∈ U ∧
      ∃ e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T,
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f := by
  let : Algebra Γ(T, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra.FinitePresentation Γ(T, ⊤) Γ(X, ⊤) := f.finitePresentation_appTop
  let : Algebra.FiniteType Γ(T, ⊤) Γ(X, ⊤) := inferInstance
  let q : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom y
  have hdim' := (affine_coordinate_fibre_dimension_eq f y).symm.trans hdim
  obtain ⟨g, hg, φ, hft, hq⟩ :=
    Algebra.exists_quasiFinite_over_polynomial_algebra Γ(T, ⊤) Γ(X, ⊤) q n hdim'
  obtain ⟨e, hefp, heqf, he⟩ := exists_chart_of_localized_polynomial_map f rfl g n φ hft hq
  refine ⟨X.basicOpen g, inferInstance, ?_, e, hefp, heqf, he⟩
  rw [← X.map_PrimeSpectrum_basicOpen_of_affine]
  exact hg

end AlgebraicGeometry
