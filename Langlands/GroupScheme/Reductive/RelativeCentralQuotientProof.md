# Central quotients of reductive group schemes

Workers 358 and 226.

`Langlands.GroupScheme.relativeCentralQuotient` proves
[`RelativeCentralQuotientStatement.{u}`](RelativeCentralQuotientStatement.md) in every
universe `u`. The theorem applies to any base scheme and any supplied fppf quotient
`q : G ⟶ G'` of a reductive group scheme by a flat central closed subgroup.
It gives reductivity of `G'`, the equality `(center G').comap q = center G`, and
the two existence clauses and the uniqueness clause for maximal tori.

The theorem applies `relativeCentralQuotient_of_multiplicativeType_inputs` from
[`RelativeCentralQuotientReduction`](RelativeCentralQuotientReduction.md), supplying
its three premises in order with the following published theorems.

1. `relativeMultiplicativeTypeClosedSubgroup` gives multiplicative type for flat,
   locally finitely presented closed subgroups of groups of multiplicative type.
   [RelativeMultiplicativeTypeSubgroupProof](../Torus/RelativeMultiplicativeTypeSubgroupProof.md)
2. `relativeCentralMultiplicativeTypeQuotient` provides an affine fppf quotient of a
   smooth affine group with connected geometric fibres by a central closed subgroup
   of multiplicative type.
   [RelativeCentralMultiplicativeTypeQuotient](../RelativeCentralMultiplicativeTypeQuotient.md)
3. The second clause of `multiplicativeTypeNormalCentral` makes the preimage of a
   central closed subgroup of multiplicative type central in a smooth affine source
   with connected residue fibres, for a quotient by a normal closed subgroup of
   multiplicative type.
   [MultiplicativeTypeNormalCentralProof](MultiplicativeTypeNormalCentralProof.md)

The reduction factors the actual kernel through the relative centre and uses
the first theorem to show that it is of multiplicative type. It compares the
supplied quotient with the affine quotient from the second theorem, then obtains
reductivity by smoothness descent and the field case on geometric fibres. The
third theorem makes the preimage of the target centre central, and flat
surjective descent of commutation gives the reverse inclusion.

For a source maximal torus, the reduction quotients it by the central kernel
and identifies the resulting maximal torus in the target and its full
preimage. For a target maximal torus, it uses local existence and conjugacy
to descend the torus property of the actual preimage, whose residue fibres
are maximal by self-centralization. Finally, equality of preimages reflects
equality of the ranges of the target maximal tori along the fppf quotient.

This proof assembles the imported group-scheme results for the proposition
corresponding to Conrad, *Reductive group schemes* (2014), Corollary 3.3.5
(pp. 100–101) and Exercise 5.5.9(i) (p. 184). The source correspondence is
recorded in the [statement](RelativeCentralQuotientStatement.md).
