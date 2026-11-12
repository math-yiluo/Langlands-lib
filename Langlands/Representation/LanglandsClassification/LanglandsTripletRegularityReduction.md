# Opposite regularity: exact reduction to the kernel and identity-support inputs

Author: Worker 135. This is an internal decomposition of the published
`LanglandsTripletOppositeRegularityStatement`, with independent universes
`u` and `v`. It does not prove that target unconditionally.

`LanglandsTripletOppositeKernelStatement` retains the full telescope and every
hypothesis of the published target, and retains exactly its first conclusion:
the twist of the Langlands inducing representation is `PQ`-regular, namely the
two split-component kernel ideals sum to the whole group algebra. The published
target and its imports remain unchanged.

`LanglandsTripletOppositeRegularityReductionStatement` asserts that the general
opposite identity-support comparison, together with this kernel assertion,
implies the exact published target. The theorem
`langlandsTripletOppositeRegularity_of_kernel_and_identitySupport` proves this
implication. It extracts admissibility from the tempered component of the
triplet predicate and irreducibility from that predicate. The published twist
invariance results transfer both properties to the unramified twist. The
kernel premise supplies regularity, and the opposite support premise identifies
the identity support image with the twist. The actual-parabolic calculation
`pqRegular_intertwining_finrank_eq_one` then gives complex finrank one through
the proved Frobenius reciprocity and admissible Schur results.

The two premises remain unproved here. In particular, this decomposition does
not establish the geometric separation of nonidentity exponents or any of the
Weyl chamber inequalities in Renard VII.4.1. Its provenance is internal: the
first premise extracts one conjunct from the existing target, and the proved
reduction assembles independently defined mathematical inputs through the new
restriction equivalence. It should not be cited as a proof of the VII.4.1 Lemma.
