# Conditional reductive parabolic and pseudo-parabolic comparison

This derived adapter compares the existing actual-subgroup predicates. Every
assertion is conditional on `ParabolicDynamicStatement`; the subgroup and
minimality equivalences also require
`HasTrivialUnipotentRadical G` over the ground field. Neither input is proved
here. In particular, this file does not identify geometric radical triviality
with ground-field radical triviality.

`IsParabolicSubgroup.pseudoParabolicPresentation` chooses a ground-field
cocharacter whose dynamic parabolic presents a given parabolic as a
represented fppf product with the unit subgroup. The dynamic structure
statement supplies the cocharacter. Multiplication by the unit subgroup does
not enlarge a represented subgroup, by `SubgroupFunctor.FppfProductTrivial`.
This choice is presentation data for the original subgroup homomorphism.

With ground-field radical triviality, the canonical unit subgroup is an
actual unipotent radical by `isUnipotentRadical_kernelUnit`. This makes the
chosen presentation a pseudo-parabolic presentation. Conversely, a
pseudo-parabolic presentation has a radical with trivial all-test image.
The affine dynamic parabolic representative is a monomorphism, so fppf
descent removes that trivial factor. The resulting range equality allows
the supplied dynamic structure statement to prove parabolicity.

Minimality then transfers in both directions by applying the corresponding
subgroup comparison to each subgroup in the original definitions. The
subgroup homomorphisms and every all-test range inequality and equality
remain the same.

The final theorem `minimalParabolicConjugacyStatement_of_pseudoParabolic`
assembles the exact existing `MinimalParabolicConjugacyStatement` from three
explicit premises: the dynamic structure statement, ground-field radical
triviality for every connected reductive group, and
`MinimalPseudoParabolicConjugacyStatement`. It applies the latter statement
to the transferred minimality proofs and retains its actual rational point,
source group scheme isomorphism, and conjugacy equation. This conditional
adapter does not establish the unconditional task target.

This route is internal interface reasoning from the published definitions
and supplied statements. Its mathematical motivation is the reductive
comparison in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition,
Proposition 2.2.9, printed pages 67–68, followed by Theorem C.2.5, printed page
595. The structural results themselves remain outside this contribution.
