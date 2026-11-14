# Bounded depth-zero root filtrations over the maximal unramified field

Worker 312. The theorem
`Langlands.Geometry.Building.MaximalUnramified.zeroRootFiltrationBounded`
proves the existing
`Langlands.Geometry.Building.MaximalUnramified.ZeroRootFiltrationBoundedStatement.{u}`
at arbitrary universe `u`.

For every nonarchimedean local field `F`, affine group scheme `G` over the
actual field `inertiaFixedField F`, supplied `C : BuildingData F G`, apartment
point `x : C.Apartment`, and relative root `a ∈ relativeRoots C.i`, the actual
subgroup `C.filtration x a 0` is algebraically bounded in `G`. The relation is
exactly `ValuativeRel.ofValuation (fixedFieldValued F).v`, as prescribed by the
unchanged statement.

## Implemented proof

The proof applies
`unramifiedZeroRootFiltrationBounded_of_henselianDiscrete_of_boundedApartment`
to the two proved inputs `Langlands.GroupScheme.henselianDiscreteQuasiSplit`
and `quasiSplitIntegerBoundedApartmentExistence`.

The first input supplies quasi-splitness from the henselian valuation ring,
surjective integer valuation, and algebraically closed residue field of the
actual inertia fixed field. The second constructs a full V 6-compatible
apartment for any prescribed maximal split torus, retaining algebraic bounds
at every apartment point. It is the depth-zero consequence of
`quasiSplitAllDepthBoundedApartmentExistence`, whose construction descends
bounded split root filtrations along torus and field restriction.

The reduction transfers full V 6 compatibility between representatives of
the same centralizer and then uses
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus` to identify
the supplied apartment class with the constructed bounded class. Rewriting
that equality yields the bound for the original supplied point and root.
`MaximalUnramified.valuation_isEquiv` supplies compatibility with the
statement's prescribed relation.

Both structural inputs are discharged by the named theorems. The result has
no additional hypotheses. It neither assumes V 7 nor uses completeness or
compactness of the inertia fixed field.

## Provenance

This is an internal composition of the three imported results. Its
mathematical content is the final assembly of henselian quasi-splitness,
bounded apartment existence, and the supplied-class transfer. The existing
target and every pair it imports are unchanged.
