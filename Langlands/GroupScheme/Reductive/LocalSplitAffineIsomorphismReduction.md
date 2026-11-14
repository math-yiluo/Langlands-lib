# The local isomorphism theorem from the affine theorem

`localSplitIsomorphismTheorem_of_affine` proves the implication from the
unchanged `AffineSplitIsomorphismTheoremStatement` to the unchanged
`LocalSplitIsomorphismTheoremStatement`, uniformly in the universe `u`.

The proof takes the original local ring, reductive groups, coordinate split
tori and fibrewise root data. For each root of each datum,
`localRootWeightSpaceEquiv` gives a linear trivialization over the original
ring. These are precisely the extra root-space hypotheses of the affine
statement. The residue-fibre maximality hypotheses are definitionally the
affine statement's `IsFibrewiseMaximalTorus` predicates. Reversing the
supplied root-pairing equivalence gives the contravariant orientation
required by the affine statement. Its resulting group isomorphism proves
the local conclusion.

This is an internal composition of the two published statements with the
local root-space construction. It has no reducedness or other additional
local-ring hypothesis. The affine isomorphism theorem remains an explicit
premise: this reduction does not by itself prove the local target or close
Task 6014.

For mathematical context, the root-space trivializations give the local
free-root-space condition in Brian Conrad, *Reductive group schemes*
(2014), Definition 5.1.1, pp.136–138. The affine input formalizes the
isomorphism conclusion of Theorem 6.1.17, p.197.
