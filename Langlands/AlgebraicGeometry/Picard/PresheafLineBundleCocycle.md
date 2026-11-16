# Naturality of coherent line-bundle transitions

This is an internal consequence of the identity and composition axioms of
`PresheafLineBundle`. It applies with independent scheme and value universes.

`pullbackIso_target` records how a named equality of families changes the
cartesian identification. `transition_eq` computes a transition through any
common restriction of its two families.

`transition_precompose` shows that the actual transition isomorphisms are natural
under precomposition of the common test scheme. The formula includes the two
canonical composition comparisons of line-bundle pullback. Its proof expands
the two composite cartesian identifications by `pullbackIso_comp` and cancels
the common final identification. Together with the published identity and
transitivity laws for transitions, this supplies coherent equivariant line
bundles for represented overlap relations. It asserts no effective scheme
descent.

`transition_overMk` compares the same transition computed after presenting the
test scheme by two equal structural maps. The equality follows from their
common chart coordinate; equality elimination then identifies the two
transitions. This comparison supplies the change of test presentation used
in the local equivariant bundle transitivity proof.
