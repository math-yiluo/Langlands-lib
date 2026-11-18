# Compatibility and effectiveness of local generator evaluation kernels

This internal development compares the actual local weighted evaluation
quotients after further original full-domain restriction. Kernel base change,
overlap compatibility of the closed extensions, and recovery of the local
kernels all assume that the projections of one finite matching tuple generate
each original local algebra as a module over its original cover algebra.
Equivalently, each projected tuple has a surjective coefficient map.

`restrictedEvaluation` is the entire bounded map from the weighted
presentation over an original subdomain to the corresponding original
closed-quotient local base change. `restrictedPushoutEquiv` identifies the
further pushout of the local evaluation with this original local base
change. Both maps and both bounds come from the constructed bounded
pushout comparison, preserving the entire further source leg.

`kernel_restrictedEvaluation` applies the published admissible-pushout
kernel theorem and injectivity of the constructed bounded equivalence.
The local finite Banach structures and surjectivity of the coefficient maps
give admissibility via `localEvaluation_isAdmissibleEpi`. The restricted
evaluation kernel is therefore exactly the closed extension of the original
local evaluation kernel. `restrictedEvaluation_overlap` proves equality of
the two entire original restricted evaluations through the supplied transition.
The global weighted leg uses the matching projection equation, and the
original intersection coefficient leg uses the transition's coefficient
equality. The resulting `kernels_overlap` compares the closed kernel
extensions on the actual pullback of the literal original intersection.

`overlapDomainEquiv` compares the literal intersection of two weighted
pullback cover members with the weighted pullback of the original literal
intersection, using equality of their exact loci. Uniqueness of full-domain
restrictions identifies the entire maps from the two original local weighted
algebras. Closed-ideal transport through that bounded equivalence then gives
`kernelCompatible` on the actual literal intersections of the weighted
pullback cover.

For every finite matching tuple, `globalKernel` is the contraction of the
original local kernels. It is closed by continuity of the finite restriction
family. `globalKernel_eq` identifies it with the kernel of the entire
matching-valued evaluation map. An element vanishes in the matching algebra
exactly when all its original projections vanish, and each projection is its
original local evaluation following the stored weighted restriction. Under the
local module-generation hypothesis, `globalKernel_local` applies the
unrestricted closed-ideal effectiveness theorem to recover every local kernel
as the closed extension of this exact global ideal.

The generic `BoundedAlgEquiv.closedIdealMap_injective` reflects equality of
closed ideals by applying the closed extension along the bounded inverse.
Closedness and the inverse identities give exact recovery of each ideal.

This is derived from actual bounded pushout and admissible-kernel APIs.
It retains arbitrary positive polyradii, trivial coefficient valuations,
and empty covers or spectra.
