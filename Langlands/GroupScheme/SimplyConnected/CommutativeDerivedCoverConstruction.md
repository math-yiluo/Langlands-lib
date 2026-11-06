# Actual derived covers of commutative connected reductive groups

This internal construction proves the concrete commutative case of actual
simply connected derived-cover existence. It uses the published
`IsSimplyConnectedDerivedCover` and `IsSimplyConnectedCover` predicates,
including the full universal property. The derived group and its cover are
the actual trivial group scheme over the same field, its ambient inclusion
is the original identity section `kernelUnit G`, and the covering map is its
identity. No cover is assumed as input.

The trivial group is isomorphic to the split torus on an empty index set,
so the existing split-torus reductivity theorem makes it connected
reductive. It represents its own entire centre and is finite over the
field; thus it is semisimple in the existing definition.

For any incoming central isogeny `q : H → 1` with semisimple source, the
identity section `1 → H` is a right inverse because maps to the trivial
group are unique. The published finite-hom cancellation theorem, applied
to the smooth connected affine source `H` and the finite map `q`, makes it
a left inverse as well. Thus `q` is an isomorphism, proving simple
connectedness of the trivial group. Its identity has the required
universal covering property: any incoming central isogeny has a unique
inverse factorization.

A separated commutative group has trivial actual derived subgroup by the
published all-test commutator-intersection theorem. The original identity
section is closed and represents exactly that subgroup. Together with the
proved universal identity cover, this gives `commutativeDerivedCoverData`
for every commutative connected reductive group at every universe `u` and
over every field. Its ambient inclusion is definitionally `kernelUnit G`.
This includes all actual field tori and can be used over the maximal
unramified field as well.

This result supplies no derived cover of a noncommutative group and no
general semisimple cover theorem. It constructs no root valuation,
parahoric building or five-axiom witness; those are separate constructions
of the parent task. Its purpose here is the actual zero-data prerequisite
in the torus case.
