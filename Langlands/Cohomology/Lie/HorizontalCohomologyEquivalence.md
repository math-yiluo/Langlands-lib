# Equivalence transport on actual horizontal cohomology

This internal construction upgrades the published equivariant horizontal
cohomology transport to equivalences. It uses the existing cycles, actual
differential-image boundaries and their module quotients. Its only direct
dependency is `HorizontalCohomologyIntertwiner`; it makes no identification with
an external cohomology theory or an automorphic realization.

The coefficient field has characteristic zero. The Lie algebra, the two
coefficient Lie modules and the acting types have the independent universes shown in
Lean. Both complexes use the same submodule `H`, group `G` and Lie-algebra action
`σ`, and separate coefficient representations `ρ` and `τ`. Bracket covariance
and the all-degree insertion identities are the same explicit hypotheses as in
the published horizontal differential. The underlying cochains are horizontal
and equivariant under every element of `G`.

An arbitrary monoid `P` acts on both cochain complexes degree by degree, with
explicit differential compatibility. The additional input `cochainEquiv`
consists of equivalences of these representations in every natural degree.
`hEquiv` says that their forward maps commute with the actual differentials.
No compatibility of the inverse maps, equivalence on cycles, or equivalence on
cohomology is supplied.

`differential_cochainEquiv_symm` derives inverse differential compatibility.
It applies the injective forward equivalence in the next degree and uses the
forward chain equation and the two inverse identities.

`equivCycles` uses the published forward cycle intertwiner and the published
cycle intertwiner of the inverse cochain equivalence. Equality of the underlying
cochains proves its two inverse identities. `equivCycles_toIntertwiningMap`
identifies its exact underlying map; `equivCycles_val` identifies its underlying
transported cochain.

`equivCohomology` uses the corresponding published quotient intertwiners in
both directions. Surjectivity of the actual cycle-to-class projection reduces
its inverse identities to the published representative formulas and the
cochain inverse identities. Its underlying intertwiner is exactly the published
quotient transport, as recorded by `equivCohomology_toIntertwiningMap`.
`equivCohomology_class` and `equivCohomology_symm_class` identify its action in
both directions on actual cycle classes.

`equivCycles_symm` and `equivCohomology_symm` identify transport of the inverse
cochain equivalence with the inverse of the constructed equivalence. Extensionality
reduces these equalities to the defining inverse maps. The two `_refl` laws
identify transport of identity cochain equivalences with identity equivalences.
For cycles this follows from equality of underlying cochains; for cohomology it
follows by choosing a cycle representative, unfolding the map to the published
quotient transport, and using its identity law.

For a third coefficient Lie module in an independent universe, the two `_trans`
laws identify transport of a composite with the composite of the transported
equivalences, applying `cochainEquiv` first and `secondEquiv` second. The composite
chain equation uses the second equation followed by the image of the first
equation in the next degree. Cycle extensionality proves the first law.
Surjectivity of the actual class projection and the representative formula
reduce the quotient law to that same equality of underlying cochains.

All local additive group structures are explicitly named canonical
`Submodule.addCommGroup` structures. The construction applies in every natural
degree, including degree zero with its existing zero boundary space.
It claims no topology, smoothness, finite dimension, nonvanishing, arithmetic
existence, analytic or sheaf comparison, or injectivity from relative to absolute
cohomology.
