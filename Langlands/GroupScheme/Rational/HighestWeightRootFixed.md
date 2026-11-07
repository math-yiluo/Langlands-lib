# Fixed highest vectors and highest-coordinate functionals

This internal derived unit starts with a supplied split pinning, full coroot
span, a supplied actual highest-weight representation, and additive-group maps
with the stated all-relative-test torus equivariance. It asserts no existence
of these structural or representation data.

`highestWeightProjector` is the existing actual torus-character projector at
the supplied highest weight. The highest-weight support condition and strict
positivity of polarized rho on nonzero positive-root combinations show that
every occurring weight has polarized-rho pairing at most that of the highest
weight.

For any character with strictly positive polarized-rho pairing, the signed
coefficient-shift theorem shows that positive-degree raising coefficients kill
the highest-weight space. The existing coefficient criterion then gives
fixedness of each highest vector under the entire supplied additive action on
every relative scheme test. For the opposite character, each positive-degree
coefficient has zero highest-weight projection: its shifted weight is strictly
below the highest weight. The full torus-weight decomposition extends this
vanishing from all weight spaces to the entire original representation space.

The functional-recovery lemmas compare coefficients of the original scalar
matrix coefficient polynomial. A functional killing all positive-degree
operators has a constant polynomial coefficient, so it is invariant at every
base-field scalar parameter, including over finite fields. Choosing a character
basis, a highest basis vector, and its coordinate functional composed with the
highest projector gives a pair with evaluation one. The vector is fixed on all
relative tests and the functional is invariant at every base-field lowering
point.

The unit derives the fixed-data premises used in the rank-one coefficient
calculation; it does not yet supply its coroot-weight premise or the root-cell
relation. The functional invariance conclusion here is stated over the base
field. Whole-unipotent top-action nonvanishing and the exact entire induced
space remain separate obligations. The provenance is the existing
highest-weight support, polarized-rho positivity, actual coefficient-shift,
fixed-vector criterion and scalar matrix-coefficient results; no external
source is invoked.
