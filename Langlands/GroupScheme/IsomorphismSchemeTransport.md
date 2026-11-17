# Transport of full Isom representatives

This internal construction follows directly from the published all-test
`LocalGroupIso`, its refinement operation, and the classification property of
`GroupIsomorphismScheme`. It uses no geometric representability theorem.

For arbitrary group schemes `G`, `H`, `K` over an arbitrary scheme `S`, an
actual group-scheme isomorphism `i : H ≅ K` postcomposes every natural local
family from `G` to `H`. At every relative test and parameter point the new
map is the original group-point isomorphism followed by `i`. Composition
preserves naturality. Postcomposition by the inverse is its inverse, as
proved using the two identities of the actual isomorphism. These bijections
commute with every parameter refinement and therefore form an isomorphism
of the full Isom presheaves.

`GroupIsomorphismScheme.postcompose` retains the supplied representative's
actual parameter scheme and postcomposes its universal family. Its
classification bijection is the original classification bijection followed
by the local-family bijection. In particular, `ofAutomorphism` turns a
supplied representative for `Aut(G)` and an actual isomorphism `G ≅ H` into
a full representative for `Isom(G,H)` with the same parameter.

All relative scheme tests are retained, without affineness, reducedness or
field hypotheses. Any geometric properties of the parameter are retained
because the parameter itself is unchanged. The construction assumes the
initial representative and the actual isomorphism; existence of those
inputs and effective descent remain separate obligations.
