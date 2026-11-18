# The clopen identity locus of a group-scheme idempotent

Worker 632.

Actual identity or triviality on an open remains such after every base
change factoring through that open. The proof uses naturality of the
direct-versus-iterated pullback comparison, so the statement concerns actual
group-scheme maps.

For a closed retract image whose group and ambient group are smooth with
geometrically connected fibres, the identity and zero opens constructed in
`IdempotentRetractLoci` are disjoint whenever the identity and trivial
endomorphisms of each ambient residue fibre differ. Indeed, a point in both
opens gives both equalities after factoring its residue-field point through
the two opens. This contradicts the supplied nontriviality condition.

A supplied residue-field identity-or-trivial dichotomy makes the opens
cover the base. Since they are disjoint, the zero open is the complement of
the identity open, proving the latter is also closed. `identityClopen`
bundles this actual part of the base as a clopen set.

The residue dichotomy and nontriviality are explicit inputs here. No
fibrewise equality is promoted directly to an equality on a nonreduced
base. Equality on the opens comes from smooth monomorphisms and the actual
retract construction. This is an internal geometric support result.
