/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux

/-! Reverse flatness comparison for a polynomial chart.

Source: Stacks Project, Tag 00R7 as applied in Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-reverse)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flatness of the canonical closed-fibre map lifts to the chart stalk map.

The proof applies the local criterion for flatness to the stalk tower. The chart
stalk is essentially finitely presented over the base stalk, is flat over the
base by flatness of the source, and its closed-fibre module is flat precisely
when the canonical polynomial fibre map is flat. The fibre and stalk
identifications transport the resulting flatness.
Source: Stacks Project, Tag 00R7 and Tag 00RH.
(blueprint: lem-sbc-polynomial-chart-stalk-flat-comparison-reverse) -/
theorem polynomial_chart_stalk_flat_comparison_reverse
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme) :
    (PolynomialChart.stalkMap f U n e he x).Flat → (e.stalkMap x).hom.Flat := by
  intro hfibre
  exact polynomial_chart_stalk_flat_comparison_reverse_aux f U n e he x
    (Flat.stalkMap f (U.ι x)) hfibre

end AlgebraicGeometry
