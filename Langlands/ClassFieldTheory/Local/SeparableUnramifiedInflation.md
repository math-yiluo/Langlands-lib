# Finite unramified inflation on separable unit cohomology

`fixedFieldUnitInflation` inflates relative cohomology of the actual
fixed field of an open normal subgroup. It identifies the units of the
fixed field with invariant units in the ambient Galois field and uses
the finite-quotient inflation to continuous cohomology. The refinement
formula identifies the map through a larger fixed field with relative
inflation followed by the map from that larger field.

In degree two, the map is injective and its image is the kernel of
restriction to the open normal subgroup. Indeed, at any refinement
the quotient actions and restriction map identify with those of the
finite tower of fixed fields. Finite Galois inflation and restriction
exactness applies, and the finite-stage exactness theorem passes it
to the actual continuous maps.

For a nonarchimedean local field \(F\), separable inertia has trivial
continuous \(H^2\) on separable-closure units. A class therefore
restricts to zero on some open normal subgroup containing inertia,
by closed-subgroup restriction zero detection. The fixed field of
that open subgroup is finite Galois and arithmetically unramified.
Inflation exactness expresses the original class as the inflation
of a relative class from this field.

This is the finite-stage form of the unramified inflation step in
Serre, *Local Fields* (1979), Chapter XIII, §3, Proposition 6,
printed pp. 192–193. The Lean proof uses the actual separable
closure in every characteristic. The finite-tower comparison adapts
the Library's algebraic-closure proof in
`Langlands/ClassFieldTheory/Local/AbsoluteH2InflationProof.lean`.
