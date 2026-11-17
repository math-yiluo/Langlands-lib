# Actual root-weight terms as ambient intrinsic cutoffs

Work over an arbitrary commutative ring. Supply a root-height chart, nonnegative secondary weights, an actual closed inclusion of the chart group into an ambient group, compatible actual torus-equivariant root maps, and an affine presentation of the ambient group. No field, smoothness, reducedness, or finite-type hypothesis is added here.

`ambientInclusion d` is the original represented term inclusion followed by the actual ambient inclusion. `torusPt_powers_eq` compares the coefficient torus with the actual fixed-exponent cocharacter. Using this comparison, `ambientInclusion_equivariant` proves that the positive-term inclusion is equivariant for the restricted original torus action and the ambient actual cocharacter-conjugation action over every coefficient algebra.

Suppose a coordinate cocharacter pairs with each supplied root as a positive natural multiplier `q` times its original secondary weight. `ambientCutoff_comap` identifies the ambient intrinsic conjugation cutoff at `q * (d + 1)`, pulled back to the actual positive term, with the original term `d` inside that positive group. Closed equivariant reflection supplies the first equality, and the polynomial coordinates on the positive term supply the second. In particular, the weights stored in the original filtration are not replaced by their multiples.

If the actual positive-term ambient inclusion represents the contracting subgroup of that cocharacter, `range_ambientInclusion_eq_cutoff` upgrades the comparison to equality of the full ambient subgroup functors on every scheme test. The forward direction factors each term through the positive group. For the reverse direction, the positive intrinsic cutoff lies in the first cutoff, which equals the actual contracting subgroup, so it lifts to the actual positive representative. The pullback comparison then lifts it to the original term representative.

The represented contracting-subgroup identification is an explicit premise of this generic theorem; the separate split face-cocharacter realization theorem proves that premise in the intended application. This unit does not itself prove parabolic normality or global compatibility/descent.

Provenance: internal combination of actual cocharacter point formulas, closed equivariant intrinsic reflection, positive-term polynomial coordinate comparison, and actual contracting representability.
