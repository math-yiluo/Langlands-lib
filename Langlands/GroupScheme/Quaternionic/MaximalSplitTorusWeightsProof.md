# Weights of maximal split tori of connected isometry groups

The theorem `Langlands.GroupScheme.Quaternionic.isometryMaximalSplitTorusWeights`
has exact type `IsometryMaximalSplitTorusWeightsStatement.{u}`. It retains the
published hypotheses at every universe `u`, with no additional rank premise,
field infinitude assumption or characteristic restriction.

The hypotheses concern a finite-dimensional central division algebra with the
specified degree and symmetric-subspace dimension, a quadratic form with invertible
polar form and smooth isometry group, and any maximal split torus of the connected
isometry group. The conclusion supplies independent actual characters of that
torus which detect every cocharacter and the stated signed-weight dimension
formula for the action tested over every commutative coefficient algebra.

The implemented argument chooses a finite splitting of the given maximal split torus.
The connected isometry group is smooth, affine and connected by the published
identity-component construction. Published maximal extension and rational conjugacy
of maximal split tori therefore identify the coordinate cardinality of this splitting
with the group's split rank. The theorem `connectedIsometrySplitRank` identifies that
rank with the quadratic Witt index. The helper
`isometryMaximalSplitTorusWeights_of_connectedIsometrySplitRank` makes this use of
the rank theorem explicit; the final theorem supplies it without adding a premise.

The closed inclusion of the maximal split torus into the connected group, followed
by the closed identity-component inclusion into the full isometry group, satisfies
`exists_characters_of_isometryTorus_rank_eq`. Its character independence,
cocharacter detection and dimension formula give precisely the claimed conclusion;
associativity identifies the composite action.

The adapter uses the inverse-right universal row-weight decomposition, singularity
of sums of nonopposite row spaces, equality of opposite dimensions from the polar
form, and integral generation of the character lattice. Equality of rank with Witt
index then forces a signed basis with multiplicity one, and grouping its weights by
the actual character–cocharacter pairing gives the count, including the residual
zero-weight term. The coefficient-algebra formulation handles finite fields and
characteristic two without a rational-point density argument.

This is an internal assembly of the actual isometry torus weight decomposition,
the connected isometry rank theorem, maximal split torus extension and smooth
affine connected rational conjugacy. It uses no classification or Kneser--Tits
consumer statement.
