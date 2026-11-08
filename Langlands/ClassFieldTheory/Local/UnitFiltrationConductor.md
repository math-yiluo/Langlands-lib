# Actual unit filtrations and the conductor criterion

This internal, derived helper identifies the two published definitions of the
unit filtration. It retains every prime, every universe-polymorphic p-adic
field, every supplied topological realization, and every natural level,
including zero. The final theorem `unitFiltrationComparison` has precisely the
published proposition `Langlands.LocalClassField.UnitFiltrationComparison`.

The proof constructs the discrete valuation's integer-ring certificate from
`mem_integers_iff_discreteValuation_le_one`. It uses the existing public
`coordinateUniformizer` and `maximalIdeal_eq_span_coordinateUniformizer` to
identify powers of the maximal ideal with the valuation balls of radius
`exp (-n)`, using Mathlib's `Valuation.Integers` ideal-power theorem. Kernel
membership for reduction on integer units then becomes the valuation condition
on the difference from one. An integer unit has valuation one. Conversely a
field unit of valuation one and its inverse are integral, giving the actual
integer unit that witnesses membership in the mapped reduction kernel.
This proves literal subgroup equality at all levels without a closure or a
positive-level assumption.

`congruenceUnitsEquivPrincipalUnits` constructs the canonical multiplicative
equivalence from the integer-unit congruence kernel to the valuation-defined
principal-unit group. Its underlying map is exactly the integer-unit inclusion,
as the accompanying coercion lemma states.

`multiplicativeConductor_le_iff_unitFiltration_le_ker` rewrites this equality
in the published least-level conductor criterion. It applies to every
continuous complex quasicharacter; no finite-image assumption appears.

Provenance is internal: these are consequences of the Library definitions and
of the public arithmetic and graded-unit-coordinate results imported by Lean.
The mathematical convention is `U^0 = O^×` and `U^n = 1 + m^n` for positive
`n`. This unit proves neither finite nor absolute reciprocity.

`filtrationValuationIntegers` is public so the unit-filtration comparison and unramified-conductor modules reuse the same integer-ring valuation witness.
