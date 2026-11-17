# Character automorphisms acting on finite diagonalizable embeddings

An additive equivalence of a character group induces an actual isomorphism
of its diagonalizable group scheme by character restriction. Identity and
composition are computed using the published all-test character-point
formula. For a finite character group, its automorphism group is finite.
The group used for parameter actions is the multiplicative opposite of the
multiplicative version of `AddAut M`: its indexing agrees with the reversed
composition order of precomposition on embeddings.

This is derived infrastructure. The generic closed-embedding action specializes
to these source isomorphisms. The imported
`Diagonalizable.restrictEquiv_baseChange_injective` proves faithful indexing
after every nonempty test base change: restriction to a residue-field point
reduces it to injectivity of character maps over a nonzero coefficient field.
Consequently `characterAction` is an actual finite free scheme action, with
no remaining faithfulness premise. Its automorphisms preserve the original
coefficient base. This constructs the action; its quotient and normalizer
orbit comparison are separate steps.
