# The indexed cocharacter in a supplied split spin comparison

This derived construction lifts a cocharacter of the actual maximal split torus
of `TitsIndexData` to the pinning torus, first over the separable closure and
then over a supplied extension field. The lift uses the given `torusMap`; the
cocharacter square is proved from the index's `square` and the existing
`splitCoverTower_cocharacter` identity. It relates the actual original
cocharacter action on the quadratic form to the actual split orthogonal action
of a supplied Morita comparison.

The generic numbered alignment lemma transports the condition at every vertex
labelled zero through the inverse of `baseChangeSimpleEquiv` and applies
`splitCoverTower_alignment`. Its kernel condition retains all relative test
schemes. This lemma requires an algebraic extension of the pinning field.

All fields are in an arbitrary common universe, with no characteristic or
cardinality restriction. The comparison and original alignment are supplied;
this unit asserts neither their existence nor the host vector-weight theorem.
The content is internal functorial transport from the existing pinning and
spin-cover comparison modules, with no separate literature assertion.
