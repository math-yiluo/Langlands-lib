/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonForward
import WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverse

/-! # Flatness comparison for a polynomial chart and its closed fibre

Source: Stacks Project, Tags 00R7 and 00RH.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A stalk map of a chart is flat precisely when its closed-fibre stalk map is flat.

Source: Stacks Project, Tag 00RH, the application of Tag 00R7 in its proof.
Proof: write A = O_{T,p}, P = O_{AffineSpace,e(x)}, and B = O_{U,x}.
The chart supplies a local tower A -> P -> B. The algebras P and B are
essentially of finite presentation over A, by polynomial finite presentation
and local finite presentation of f restricted to U. The module B over itself
is nonzero and finitely presented; it is A-flat because f is flat and U is open.
The local rings of the closed fibres are P/m_A P and B/m_A B, identified
with PolynomialChart.sourceStalk and the actual fibre stalk by the canonical
base-change stalk isomorphisms and the inverse stalk map of the open immersion.
Under these identifications the induced local map is PolynomialChart.stalkMap.
If the original stalk map is flat, tensor base change and localization make
this map flat. Conversely, flatness of this map is the closed-fibre module
hypothesis of Tag 00R7 for M = B in the tower A -> P -> B. Its other hypotheses
were checked above, so the criterion makes B flat over P. The identifications
preserve flatness and recover the displayed equivalence. Quasi-finiteness is
not required for this comparison.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison) -/
theorem polynomial_chart_stalk_flat_comparison
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (e.stalkMap x).hom.Flat ↔ (PolynomialChart.stalkMap f U n e he x).Flat := by
  constructor
  · exact polynomial_chart_stalk_flat_comparison_forward f U n e he x
  · exact polynomial_chart_stalk_flat_comparison_reverse f U n e he x

end AlgebraicGeometry
