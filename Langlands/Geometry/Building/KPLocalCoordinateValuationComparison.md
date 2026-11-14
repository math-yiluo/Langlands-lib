# Coordinate valuation comparison over the maximal unramified field

Lean module: `Langlands.Geometry.Building.KPLocalCoordinateValuationComparison`.
The definitions and comparison lemmas are in
`Langlands.Geometry.Building.MaximalUnramified`.

This internal support module defines `geometricCoordinateAddValuation f` by
pulling back the normalized additive valuation
`LocalField.algebraicExtensionAddValuation F (SeparableClosure F)` along a
supplied algebra embedding `f : E →ₐ[inertiaFixedField F] SeparableClosure F`.
Here `F` is a nonarchimedean local field in arbitrary characteristic and universe,
and `E` is a field in any universe with an algebra structure over the actual
maximal unramified field `inertiaFixedField F`. The definition itself needs no
finite degree or separability assumption.

For a finite separable extension `E` and any
`hH : HenselianLocalRing (MaximalUnramified.valuation F).valuationSubring`,
`geometricCoordinateAddValuation_eq` proves equality with the existing valuation
`FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F) hH E`.
The pointwise theorem `henselianSeparableAddValuation_eq_geometric` rewrites the
coordinate value of `x : E` as the geometric value of `f x`. This is exact
equality, including the value at zero, with no positive scaling factor.

The proof first calibrates the geometric valuation on `inertiaFixedField F`.
For every nonzero `x` in that field, `fixedFieldValuesFromBase` supplies an element
`a : F` with the same multiplicative spectral value. The equivalence
`MaximalUnramified.valuation_isEquiv` gives the same equality of integer values.
Then `valuation_base`, `Plancherel.fieldOrderUnits_toAdd`, and
`algebraicExtensionAddValuation_base_unit` identify both normalizations.
This establishes `geometricAddValuation_base`.

The helper `FieldTheory.addValuation_norm_of_invariant` applies to an additive
valuation on a Galois extension, invariant under its base algebra
automorphisms, and to a finite separable field embedded there whose relevant
minimal polynomial splits. Conjugate roots have equal values, by
`minpoly.exists_algEquiv_of_root'`. The formula
`Algebra.norm_eq_prod_roots`, the root count, and multiplicativity show that the
value of the embedded norm equals the extension degree times the value of the
element.

Apply this helper to the geometric valuation on `SeparableClosure F` over
`inertiaFixedField F`. Automorphisms over the latter field restrict to
automorphisms over `F`, so
`algebraicExtensionAddValuation_invariant` supplies invariance. Separably closedness
supplies splitting. The norm formula
`henselianSeparableAddValuation_norm` gives the same degree multiple for the
Henselian coordinate valuation. The base calculation identifies their norm
values. For nonzero elements, both values are finite real numbers and the
positive finite field degree cancels; zero is handled separately.

The provenance is internal: this construction and its lemmas are deductions from
the already published valuation constructions and field norm identities. No
unproved proposition is assumed, and this support module does not by itself
prove the torus action statement for building filtrations.
