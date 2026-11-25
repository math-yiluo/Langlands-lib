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
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Dimension
import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.Chart

/-! # Quasi-finite polynomial charts at a fibre point

Source: Stacks Project, Tag 00QE.
(blueprint: lem-sbc-quasi-finite-polynomial-chart)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A finitely presented affine morphism has a quasi-finite polynomial chart near any point,
with the number of variables equal to the dimension of the fibre at that point.

Source: Stacks Project, Tag 00QE; the affine translation used in Tag 00RH.
Proof: Write the affine morphism as Spec B to Spec A, using the canonical affine
isomorphisms. The fibre at the image of y is the spectrum of a finite type algebra
F over the residue field. Its dimension at the corresponding point is a finite
natural number n: F is finite type over a field, and the point has a nonempty
neighborhood of finite dimension. Apply Tag 00QE to A to B and this n. It supplies
b outside the prime of y and an A-algebra map A[t_1,...,t_n] to B[1/b] which is
quasi-finite at every prime. Take U to be the principal affine open D(b), and
transport the spectrum morphism to e from U to affine n-space over T. The
A-algebra compatibility says that e followed by projection equals U.ι followed
by f. The original finite presentation over A remains a finite presentation over
A[t]: from B = A[x]/(r), adjoin the relations t_i - p_i(x), including the
localization generator and relation. Thus e is locally of finite presentation.
The fibre homeomorphism and the affine isomorphisms preserve dimension at the
point, giving the asserted dimension equality. No nonempty-point assumption
needs to be added: the quantified point y excludes an empty source.
(blueprint: lem-sbc-quasi-finite-polynomial-chart) -/
theorem exists_quasiFinite_polynomial_chart
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFinitePresentation f] (y : X) :
    ∃ U : X.Opens, IsAffine U.toScheme ∧ y ∈ U ∧
      ∃ (n : ℕ) (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T),
      LocallyOfFinitePresentation e ∧ LocallyQuasiFinite e ∧
      e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f ∧
      topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_fiber_dimension_nat f y
  obtain ⟨U, hU, hy, e, he₁, he₂, he₃⟩ :=
    exists_quasiFinite_polynomial_chart_data f y n hn
  exact ⟨U, hU, hy, n, e, he₁, he₂, he₃, hn⟩

end AlgebraicGeometry
