# Fixed relation for the supported regular comparison

Author: Worker 165.

This helper module is a small composition used in the proof of
`Langlands.GLSupportedRegularWeylConeComparisonStatement`. It is not a
separate statement or a completed proof of that target.

`fixedRelation_of_nestedParameter_eq` takes two direct fine refinements and
the coordinate equality provided by the published unitary real-exponent
rigidity proof. It deduces the target fixed relation for the same permutation.
It has no representation carrier or field parameters.

The proof evaluates the input equality at the source coordinate `w.symm a`.
Unfolding `nestedParameter` and applying
`UnitaryWeylRigidity.flattenBlockEquiv_symm_blockIndex` identifies the parent
coarse labels. Negating the resulting equality gives the required
`v1 - t1 = v2 - t2` relation.

The full comparison must obtain this input equality from the second clause of
`glUnitaryWeylRealExponentRigidity`, or its helper
`UnitaryWeylRigidity.coordinate_exponent_eq`, after supplying an actual twisted
equivalence. Cuspidality supplies the admissibility hypothesis. The
reduction in `SupportedRegularWeylConeReduction` supplies the actual
equivalence.
This helper selects no permutation and establishes no occurrence, continuation,
or cone assertion. Its provenance is internal composition of the named Library
results.

`fixedRelation_of_twistedEquiv` implements that representation-theoretic
specialization for actual irreducible cuspidal unitarizable fine
representations. The proof applies
`UnitaryWeylRigidity.coordinate_exponent_eq` to the supplied actual twisted
equivalence and then uses the numerical helper. Its three universes are the
independent field and two carrier universes. It also permits rank zero.
