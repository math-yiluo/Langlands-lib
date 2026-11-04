# Dynamic quotient lifting through the fixed torus envelope

This internal construction combines the existing opposite dynamic cell,
the exact homogeneous-quotient restriction to the fixed torus envelope,
and the density-to-lifting argument. It retains the supplied target `Q`,
projection `q`, and right-coset fiber relation on every relative scheme.
It applies at arbitrary universe over every field satisfying its explicit
hypotheses.

For a smooth affine group and a subgroup representing `P(χ)`,
`Dynamic.parabolicIdentitySection` constructs an open of the supplied quotient
containing its identity coset and an actual section into the group. The
opposite subgroup is the existing affine representative of `U(-χ)`.
The proved opposite-cell theorem makes its multiplication with `P(χ)`
an open immersion. The existing quotient-cell descent then constructs the
section on the actual open image. The returned data include the identity
range containment and exact section equation.

`Dynamic.rational_lifts_of_dense_parabolic` applies the existing quotient
orbit and density argument to this section. It assumes actual rational-point
density of the group, with no reductivity or infinitude premise. The
identity section is constructed in the proof. The chosen
`Dynamic.rationalLiftOfDenseParabolic` is an actual rational group point;
its companion theorem proves its image under the original `q` is the
specified point.

`TorusGeneratedEnvelope.rational_lifts_dynamic` assumes a smooth representative
of the fixed ground-field torus envelope, normality of its inclusion on all
relative tests, and density of its actual rational points. The ambient group
is smooth, connected and affine. The stabilizer is a closed subgroup whose
all-test range is `P(χ)`. Restriction uses the affine representative of
`P(cocharacterFactor χ)` inside the envelope. The restriction construction
retains `Q` and uses the inclusion precomposed with `q`; it supplies smoothness,
surjectivity, quasi-compactness and the exact fibers. The preceding argument
produces a rational point in the envelope, and composition with its inclusion
gives the asserted point of the original ambient group.
`rationalLiftDynamic` chooses such a point and `rationalLiftDynamic_comp`
proves its exact image under the original projection.

The provenance is an internal composition of the imported definitions and
proved interfaces. Normality and density of the fixed envelope remain explicit
structural inputs here. General pseudo-parabolic stabilizers still require
the split-radical reduction and residual dynamic presentation. This unit does
not prove the full all-field pseudo-parabolic rational-lifting statement.
