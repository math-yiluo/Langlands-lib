# Restriction to unitary split weights

This internal derived construction specializes `ScalarTargetWeightRestriction`
to the existing normalized real parameter on an actual split torus. In its
intended Jacquet application, it removes the need to prove full temperedness
of the square-integrable target merely to restrict maps to unitary weights.
It introduces no external mathematical input.

The coefficient field of the representations is complex. The local field
`F` has arbitrary characteristic and universe `u`. The actual split torus
`A` has a supplied `IsSplitTorus A.toGrp` witness. The represented locally
profinite group `H`, its source and target carrier universes are independent
of `u` and of each other. A supplied homomorphism `j : A(F) → H` has central
image. No continuity or injectivity premise is imposed on this map in these
restriction lemmas.

`Plancherel.SplitTorus.normalizedRealPart_eq_zero_of_norm` proves that a
pointwise norm-one character of `A(F)` has zero existing normalized real
parameter, without an open-kernel or continuity premise. Applying the
published character-dual equivalence and testing pure tensors reduces the
claim to the definition of the lattice-section logarithm, where every
logarithm of a norm is `log 1 = 0`. This is only the stated implication; it
does not assert the converse for nonsmooth characters.

`splitUnitaryWeightRestriction` is the published scalar-target restriction
map specialized to the predicate `normalizedRealPart hA χ = 0`. Its source
is the actual algebraic intertwiner space and its target is the intertwiner
space from the existing `selectedWeightPart` subrepresentation. No new
weight space or replacement action is defined.

For an admissible source and a supplied `UnitaryCentralCharacter` of the
target, restrict that central character along `j`. Its scalar action is the
target's original action on the split points, and its pointwise norm is one.
The normalized parameter is therefore zero by the first lemma. The published
scalar-target restriction injection applies. Injective-linear-map rank
monotonicity gives `hom_rank_le_splitUnitaryWeights`, with no carrier resizing
or finite-dimensionality premise.

Finally `hom_rank_le_splitUnitaryWeights_of_squareIntegrable` extracts the
unitary full-center scalar character already contained in
`IsSquareIntegrableModCentralSubgroup C hC σ qMeasure`. The subgroup `C` is the
specified central normal subgroup, and `qMeasure` is its supplied quotient Haar
measure. The conclusion concerns the given actual split-point action `j`;
this result does not change the quotient or require it to be the full center.
The additional square-integrability and target-admissibility components
are not used by this elementary restriction step.

For the host application, `H` may be the literal Levi point subgroup, `ρ`
the actual same-parabolic Jacquet action on induction, and `j` the supplied
split-component point homomorphism. The exact lemma still requires source
admissibility and a future bound on Hom from the selected part. This module
does not supply Jacquet admissibility, identify a finite Weyl indexing group,
construct a conjugate decomposition, or prove the host generic-irreducibility
target.
