# The identity component of a maximal-torus centralizer

`Langlands.GroupScheme.torusCentralizerNormalizer.{u}` proves exactly the
published `Langlands.GroupScheme.TorusCentralizerNormalizerStatement.{u}`.
The statement and its imported pairs are unchanged. Its hypotheses include an
arbitrary algebraically closed field, a smooth connected affine ambient group,
a maximal torus, and any closed connected presentation of the identity component
of the torus centralizer through the stated maximality property. The conclusion
is smoothness, geometric nilpotence in the Library sense, and the containment of
every connected closed normalizing subgroup. No extra hypotheses are imposed.

The original source is Milne, *Algebraic Groups* (2017), Proposition 17.28, as
recorded and compared with the Lean encoding in
[`TorusCentralizerNormalizerStatement`](TorusCentralizerNormalizerStatement.md).
This proof uses the published Cartan structure and connectedness theorems, then
an internal commutator-family rigidity argument. It need not follow Milne's
unipotent-times-torus decomposition route.

First choose a full closed representative of the maximal-torus centralizer by
`exists_isCartanSubgroup_of_isMaximalTorus`. That representative is connected by
`IsCartanSubgroup.connectedSpace`, which uses connectedness of torus centralizers.
The maximality assumption on the supplied subgroup `c` therefore contains this
full representative. Together with its assumed inclusion in the centralizer,
this gives `range c = torusCentralizer j`. Consequently `c` itself is a Cartan
subgroup. Applying `cartanStructure` directly supplies smoothness and nilpotence;
no transport to an isomorphic subgroup is needed.

For the last clause, a connected closed subgroup `h : H → G` is affine because
it is a closed subgroup of the affine ambient group. The torus splits over the
algebraically closed base, using the published finite Galois splitting theorem
and its split-reflection adapter. The torus image is contained in its own
centralizer, hence in `range c`; and the hypotheses say that `range c` centralizes
the torus. Apply
`range_le_torusCentralizer_of_connected_normalizer_splitTorus` to this subgroup
functor and `h`. It shows that `range h` centralizes the torus on all scheme tests.
The established equality identifies this centralizer with `range c`, which is
the required conclusion. In particular, the argument never assumes that `H` is
smooth or reduced.

The three accompanying internal modules explain the new rigidity input:

- [`ConnectedCoefficientRigidity`](../Torus/ConnectedCoefficientRigidity.md)
  proves matrix-weight rigidity over coefficient rings with connected spectrum,
  without assuming reducedness.
- [`ConnectedPointedHomFamily`](../Torus/ConnectedPointedHomFamily.md) specializes
  universal points to prove triviality of a connected pointed family of
  homomorphisms from a diagonalizable group.
- [`ConnectedCentralizerNormalizer`](../Torus/ConnectedCentralizerNormalizer.md)
  applies that result to commutators. A normalizing connected group conjugates
  torus points into the subgroup functor; centrality makes the commutator family
  multiplicative in the torus parameter, and it is trivial at the identity of
  the connected group. Universal commutation on an affine product extends the
  result to every scheme test, and split-torus coordinates transport the result.

The theorem is universe general. Development compilation and declaration
inspection report only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
Independent semantic review and publication remain separate acceptance steps.
