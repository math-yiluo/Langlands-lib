# Supercuspidal regularity and the central denominator bound

This internal derived unit works with the canonical topology of the supplied
p-adic field and arbitrary quotient measure. It explicitly assumes the full
`SupercuspidalKirillovStatement` and the actual equal-rank analytic conclusion.
The denominator bound additionally assumes that the second representation σ
is irreducible and admissible, that the quotient measure is invariant, and
that P is a supplied normalized generator of the actual equal-rank rational
values. Laurent regularity for tests vanishing at zero does not require
these two representation-theoretic hypotheses on σ. This unit does not
assert the Kirillov statement or the final equal-rank L-factor formula.

For an irreducible supercuspidal representation and a nonzero standard
Whittaker functional, apply the compact-support conclusion of the Kirillov
statement to each vector obtained by acting on the original vector. The
representation law then supplies mirabolic compact support for every right
translate of the actual coefficient. The definition `compactCoefficientStabilizer` constructs a compact open
right stabilizer by intersecting a smooth vector's open stabilizer with the
compact level-zero subgroup. This subgroup fixes the full coefficient function.

These are precisely the support inputs of `EqualRankCompactLaurent`. The
analytic conclusion supplies convergence on a right half-plane, and its
canonical rational continuation is therefore a Laurent polynomial whenever
the row test vanishes at zero. No auxiliary analytic regularity hypothesis
remains at this step.

Finally, for an irreducible admissible second representation σ, the actual
inverse-uniformizer central recurrence, obtained by Schur's lemma for both
representations, is applied with evaluation of the row test at zero. Row translation
preserves this functional, while the previous argument proves Laurent
regularity on its kernel. For the supplied normalized generator P, the
general central denominator bound gives a
nonzero scalar c for which the normalized denominator P divides
X^(n+1) - c. This binomial is separable over the complex numbers; consequently
P is separable and squarefree as well. Identifying its roots with the
contragredient twist parameters remains a separate obligation.
