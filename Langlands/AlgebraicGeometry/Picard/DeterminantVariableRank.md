# Determinant lines from frames of variable finite rank

This internal construction starts with an actual module sheaf `M` on a scheme
`X`, an open family `T i`, a natural number `n i` for each chart, and actual
isomorphisms from the free sheaf indexed by `ULift (Fin (n i))` to `M.over (T i)`.
The chart index and the scheme have the same universe. The rank may vary from
chart to chart. No nontriviality assumption is imposed on section rings.

`basis` reindexes the actual section basis of each supplied frame by the
equivalence from `ULift (Fin (n i))` to `Fin (n i)`. The basis is defined on
every open contained in that chart. `basis_restrict` and
`basis_repr_restrict` inherit restriction compatibility from the underlying
frame sections and their coordinate morphisms.

`unit` applies `FiniteBasisDeterminant.unit` to the two bases on a common
smaller open. For equal ranks its value is the determinant expressing the
second frame in the first frame. Unequal ranks force the section ring to be
trivial by invariant basis number; in that case the unit is its unique unit.
The identity and composition laws follow from the mixed finite-basis
determinant laws. `unit_restrict` uses compatibility of basis coordinates
with restriction and `FiniteBasisDeterminant.map_unit`.

`cocycle` takes these units on the pairwise chart intersections. Restriction
compatibility and the composition law prove the triple-overlap cocycle law.
When the supplied opens cover `X`, `lineBundle` is the actual locally free
rank-one module sheaf obtained from this cocycle by `CocycleGluing`.

The provenance is derived: the module combines the existing actual section
bases, mixed finite-basis determinant units and cocycle gluing. It does not
assert that a given sheaf has such finite frames. Independence of the cover,
pullback coherence for variable ranks, a parabolic Lie polarization and its
ampleness remain separate obligations.
