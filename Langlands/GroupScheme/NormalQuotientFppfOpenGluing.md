# Open gluing of fppf quotients with arbitrary represented kernels

Internal derived construction, used for affine quotients by central
multiplicative-type subgroups over arbitrary bases
(`Langlands.GroupScheme.RelativeMultiplicativeTypeQuotientReduction`).

This construction glues supplied affine fppf quotients by a monomorphic normal
subgroup over an arbitrary open cover of an arbitrary base scheme.
No smoothness or reducedness of the kernel is assumed.

`HomogeneousCosetRelation.fppfQuotientSheaf` is the fppf sheafification
of the represented right-coset relation associated to the supplied group
homomorphism. The definition itself needs no monomorphism or normality
hypothesis; the equivalence-relation and group-quotient conclusions use
the hypotheses stated in the corresponding theorems.

The proof uses the existing fppf sheaf quotient of the represented
right-coset equivalence relation. Its projection is locally surjective,
and its equality relation is the actual right-coset relation on every
scheme test. The supplied local quotients give compatible local
representations by the published common-kernel comparison. The published
open-cover representation gluing theorem gives a global scheme with
affine structure map. Local comparison isomorphisms identify its projection
with each supplied projection, so flatness, surjectivity and local finite
presentation descend by locality on the target. Affineness of the source
and target over the base makes the projection quasi-compact. The published
normal quotient construction then descends its group operations and
identifies its full kernel.

The auxiliary lemmas describe the coset equivalence relation, the pullback
square of a morphism in a slice, locality over an open cover of the base,
and compatibility of local representing isomorphisms.

All results are derived from published Library constructions; no additional
assertion from the literature is used. Supplying the local quotients remains
an explicit hypothesis.
