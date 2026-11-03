# Regular refinements of actual cocharacters

Author: Worker 1270.

This internal construction combines the published actual-root finiteness,
generic-cocharacter choice and integral perturbation bound. For every
homomorphism `i` from a split torus into an affine group scheme locally of
finite type over an arbitrary field, `regularRefinement hT i nu` is an actual
cocharacter of that same torus. It requires neither maximality nor
reductivity, smoothness, perfectness or a restriction on characteristic.

Let `eta` be the existing `genericCocharacterOfIsSplitTorus hT i`.
The actual roots are finite by `IsSplitTorus.finite_relativeRoots`.
The natural number `regularRefinementMultiplier hT i` is the existing
`IntegralPerturbation.bound` for their integral pairings with `eta`, namely
one more than the largest absolute pairing. The refinement is this positive
multiple of `nu` plus `eta`. No new generic-direction constructor or
root-system premise is introduced.

`regularRefinement_signs` specializes the published lexicographic sign
formula. On each actual root, a nonzero original pairing determines the
refined sign, and an original zero pairing is resolved by `eta`.
The published generic specification is definitionally the regularity
condition on these roots. Consequently `regularRefinement_isRegular`
proves that all refined root pairings are nonzero.
`regularRefinement_nonneg` proves that every nonnegative refined pairing
was nonnegative originally, by excluding a negative original pairing.
`regularRefinement_pos` proves that every positive original pairing stays
positive. The construction also applies to the empty root set and to
rank-zero tori.

The provenance is an internal deduction from
`Absolute.RegularPerturbation`, `Rational.RootSupportFiniteness` and
`Rational.GenericCocharacter`; the proof route is the explicit integer
bound and sign computation above. This module establishes root-pairing
comparisons. It does not establish a comparison of dynamic subgroup
functors, Borel containment or parabolic classification.
