# Compact quotient approximation for weighted comparisons

Author: Worker 396.

This internal derived helper constructs compact induced truncations of an
arbitrary smooth induced function on the actual left-coset quotient. It supplies
the approximation step needed to extend compact character synthesis to
integrable weighted comparisons. It proves no Fourier endpoint or gamma equation.

For a closed subgroup of a locally compact nonarchimedean group, every compact
set of left cosets lies in a compact clopen set. If the group is sigma compact,
these sets give an increasing compact clopen exhaustion of the quotient, with
every point belonging to all sufficiently late sets. The proof uses compact
clopen quotient neighborhoods, a finite subcover, and a compact covering of the
quotient obtained from the continuous surjective group projection.

For any actual smooth induced function, `compactCutoff` multiplies its values
by the indicator of one such quotient set. The published smooth quotient cutoff
preserves the same inducing representation and one uniform open right
stabilizer. Its closed projected support is contained in the chosen compact
set, so it is an actual member of `CompactFunctions`. Along an exhaustion its
values eventually equal the original values at each group element.

The weighted integral results use an arbitrary supplied measure on an arbitrary
measurable parameter space, a measurable map from that space to the group, and
an arbitrary complex weight. They assume genuine integrability of the original
weighted pullback. Each weighted cutoff is its product with the measurable
indicator of the pulled-back quotient set; hence it is genuinely integrable
and its norm is bounded by the original integrand's norm. Eventual pointwise
agreement and dominated convergence prove convergence of these actual complex
Bochner integrals for the same supplied measure. There is no change of measure,
character, determinant weight, or normalization in this argument.

Finally, `weighted_integral_eq_of_compact` uses one such exhaustion to extend an
identity between two weighted integrals from every `CompactFunctions H σ` to a
given `SmoothFunctions H σ`. The two parameter spaces, supplied measures,
measurable group-valued maps, and complex weights can differ. The hypotheses
include genuine integrability of both limiting weighted functions. Applying the
compact identity to each common cutoff gives two sequences of equal integrals;
their dominated-convergence limits are equal by uniqueness of limits in
`ℂ`. This is a conditional compact-support reduction, with the compact identity
still an explicit premise.

Provenance is internal. The construction reuses the published
`Induction.CompactQuotientCutoff` and `Induction.CompactQuotientProof` APIs and
Mathlib's compact-covering and dominated-convergence theorems. Specializing the
inducing representation to the supplied scalar character retains that character.
The limiting integrability hypothesis is explicit; no desired matrix Fourier
comparison or rank-one functional equation is used to obtain it.
