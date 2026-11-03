# Transport of central isogenies by isomorphisms

This internal helper module proves invariance of the `IsCentralIsogeny`
interface under isomorphisms of the source and target over an arbitrary base
scheme in any universe. It uses the conventions and sources documented in
`CentralIsogeny/Basic.md`; it introduces no new mathematical definition or
existence assertion.

`IsCentralIsogeny.comp_iso` preserves the existing finite-flat-surjective
predicate by composition with the isomorphism, and preserves local finite
presentation by composition. A point killed by the composite was already
killed by the original map: cancel the target isomorphism on test-scheme
points. The original kernel condition then gives its centrality.

`IsCentralIsogeny.iso_comp` uses the same scheme-level composition lemmas. A
point in the new kernel maps into the old kernel, and the published all-test
centre transport along the source isomorphism returns its centrality to the
new source. The two `_iff` lemmas apply these constructions in both directions
using the inverse isomorphism. The proofs retain nonreduced kernel and centre
information throughout.
