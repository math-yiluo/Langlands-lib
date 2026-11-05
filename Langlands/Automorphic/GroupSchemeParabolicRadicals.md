# The intrinsic unipotent-radical family of rational parabolics

This internal adapter connects the existing algebraic-group program to the
all-parabolic constant-term indexing needed by the automorphic program. It works
over an arbitrary field and retains the actual group schemes and their subgroup
functors. `ProperRationalParabolic` contains exactly the existing rational
parabolic subgroup functors whose all-test image is different from the full
subgroup functor. It does not restrict to a chosen split torus, standard
parabolics, or maximal block subgroups.

`IsRationalParabolicRadical P U` says that an actual parabolic embedding presents
`P`, that an actual represented ground-field unipotent radical lies inside its
source, and that their composite has all-test image `U`. The represented radical
uses the existing greatest smooth connected normal unipotent closed-subgroup
predicate. This relation is Prop-valued; it supplies no new algebraic-group
structure or assumed analytic conclusion.

The main uniqueness argument starts with two closed presentations of the same
parabolic functor. The existing represented-subgroup isomorphism commutes with
their embeddings. Transporting the first radical along that isomorphism gives
a radical of the second presentation. Existing greatestness identifies their
images, and postcomposition identifies the ambient images. Consequently the
relation determines at most one `U`, and that image lies in `P`.

Existence is conditional on `ParabolicDynamicStatement`, kept as an explicit
argument, and on connected reductivity of the ambient group. The existing
conditional parabolic-connectedness consequence, together with the public
`dynamicConnected` proof, gives connectedness of each parabolic. Closedness
supplies affineness, and parabolic smoothness is already part of the existing
predicate. The public `unipotentRadicalExistence` then constructs its represented
ground-field radical. This is an application of those exact public results;
the parabolic–cocharacter theorem is not proved or silently assumed here.

`rationalParabolicRadical` chooses the resulting unique ambient image. Its
comparison theorem identifies it with the composite image of every actual
represented radical of every presentation of that parabolic.
`properRationalParabolicRadicals` indexes these images by all proper rational
parabolic functors, and the final comparison theorem inserts any actual proper
parabolic embedding into that family. No compactness, measure, convergence,
finite volume, square integrability, density or GL comparison is asserted.

Provenance is internal. The adapter uses the published all-test parabolic
predicate, represented-subgroup uniqueness, radical transport and greatestness,
and the stated exact existence/connectedness results. Its purpose is to make
those existing algebraic exports usable by the ensuing analytic constructions.
