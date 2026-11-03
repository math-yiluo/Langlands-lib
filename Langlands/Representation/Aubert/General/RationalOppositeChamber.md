# The reversed chamber and actual opposite rational subgroups

Worker 480. This derived comparison identifies the actual opposite dynamic
subgroups used by the rational Jacquet functor with the published standard
subgroups in the reversed chamber. It preserves the literal simple-root labels.

The root lemmas assume that the actual relative-root set is closed under
negation. This assumption follows from the existing
`HasRelativeRootSystem.neg_mem_relativeRoots`, a split torus and the published
relative-root-system realization. Thus the self-association target's `hRoots`
and maximal splitness supply it. It is retained explicitly here because some
other rational representation targets do not include `hRoots`.

`IsGenericCocharacter.neg` follows from bilinearity of the integer lattice
pairing. Simultaneous negation of a root and the chamber cocharacter preserves
their pairing and positive-root membership. A decomposition into two positive
roots in one chamber negates to such a decomposition in the other chamber.
This proves `neg_mem_simpleRelativeRoots_iff` for the published definition of
simple roots, including nonreduced and empty relative-root systems.

`IsStandardCocharacter.neg` negates the character subset and the standard
cocharacter. The zero pairings stay zero, and strict positivity on the
complement is transported by simultaneous negation. The cocharacter identity
The existing `groupHom_neg_comp_eq_oppositeCocharacter` proves that this lattice negation is
exactly precomposition with the minus-one power map used in
`Dynamic.inverseCocharacter`.

`standardSubgroups_reversedChamber` applies the original
`StandardCocharacterStatement` in both chambers. Its comparison for `-ζ`
identifies the reversed standard parabolic and unipotent subgroup with the
dynamic subgroups of the inverse cocharacter, on every test scheme. The
centralizer equality `Dynamic.centralizer_inverseCocharacter`, followed by the
original standard Levi comparison for `ζ`, identifies the two standard Levis.
No existence of a standard cocharacter is assumed beyond the supplied actual
witness `ζ` and its published standardness predicate.

`oppositeSimpleRootEquiv` is actual character negation on the two simple-root
subtypes. Its inverse also negates characters. `oppositeIndex` maps a finite
face along this equivalence, and `rootSet_oppositeIndex` proves that the
resulting character subset is exactly the negative image of the original one.
The finite-index comparison theorems evaluate the all-test comparisons at the identity
test object. They identify the actual rational-point opposite parabolic,
unchanged Levi, and opposite radical with their reversed standard families.
`oppositeSubgroups_eq_reversedStandardPoints` gives the same three equalities
directly for a character subset. It derives negation closure from the
root-system realization and maximal splitness, so it adds no negation-closure
premise at the self-association target's scope. Its radical equality identifies
the opposite with the definition used by
`BruhatTits.SpecialCompact.standardOppositeUnipotentPoints`.

All constructions work over every field in universe `u` and use the original
group scheme and actual rational-point groups. They add no restriction on
characteristic, splitting of the ambient group, quasisplitness, or the
presence of roots. They do not involve representation carriers or topology.
They do not prove a compact-open basis, natural Jacquet duality, a square
integrability criterion, irreducibility, or rank-one self-association.

The provenance is internal: the proofs expand the published positivity,
simplicity, standardness, root subset and standard subgroup definitions,
and compose their existing standard-cocharacter and inverse-centralizer
comparisons. No additional literature theorem or representation-theoretic
result is asserted. The imports are
`RationalOppositeParabolic` and `RelativeRootStandardCocharacter`.

`Dynamic.inverseCocharacter` and `Dynamic.oppositeCocharacter` have the same defining minus-one-power precomposition, so this module reuses the existing theorem.
