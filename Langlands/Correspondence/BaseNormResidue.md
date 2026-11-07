# Finite norm-residue laws for the supplied base candidate

This internal consequence concerns the actual base candidate constructed in
`BaseReciprocityCandidate`, for an arbitrary prime and finite extension of
`Q_p`. A supplied common-closure family and its norm compatibility remain
explicit premises. It does not construct such a family.

Finite restriction of the inverse candidate at the reciprocity image of a
Weil element is the restriction of that element's actual Galois projection.
The norm square identifies the kernel of each finite abelian restriction
with the actual norm image, using the existing range criterion for the
abelianized Weil fixing subgroups. The bottom field's canonical field
equivalence transports its determinant norms to those over the original field.

The actual Weil projection is dense. Restriction to a finite discrete
Galois group is therefore onto. These finite surjections also give density
of the induced map to the absolute Galois abelianization, by the existing
finite-quotient reconstruction theorem. Restrictions are compatible because
they are actual Galois restrictions.

`BaseProfiniteNormResidueStatement` collects these conclusions, with a proof.
It retains the supplied family and norm relation. With the supplied family's
full normalization premise, the existing geometric order result also gives
`LocalReciprocityCandidateRelation`. Equality of compatible base candidates
transfers that conclusion to any candidate satisfying `IsBaseReciprocity`.

The residue-action condition in full geometric reciprocity remains a separate
obligation. This unit does not prove the closed supercuspidal correspondence.
