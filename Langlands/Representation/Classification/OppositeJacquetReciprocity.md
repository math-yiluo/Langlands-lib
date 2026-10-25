# Opposite Jacquet reciprocity for actual block parabolics

This internal construction extends the published
`OppositeSupportJacquetAdapter` with the inverse orbit map. For an actual
block shape and a smooth representation `π`, `reciprocityEquiv` is a complex
linear equivalence between intertwiners from `π` to the actual opposite
normalized induction of `σ` and intertwiners from the actual opposite
normalized Jacquet representation of `π` to `σ`.

The inverse sends a Jacquet map `A` to the function
`v ↦ (g ↦ A([π(g)v]))`. The actual opposite Levi decomposition removes
the unipotent part of every opposite-parabolic element on coinvariants.
The normalized Levi intertwining equation then gives covariance with
the inverse upper half modulus. Smoothness of `π` gives a uniform open
right stabilizer for each orbit function. Evaluation at the identity
is the previously published forward construction. Evaluation of a
translate proves one inverse law; surjectivity of the quotient map and
`π(1)v = v` prove the other.

The Jacquet action is the published `OppositeSupport.jacquetAction`,
which uses the actual opposite unipotent quotient and inverse full upper
modulus. Its multiplier is the positive upper half. The induced covariance
uses the negative upper half; the cancellation is proved in
`jacquetMap_covariance`. No character sign or parabolic orientation is
changed implicitly.

For irreducible source and target, `quotient_iff_embedding` identifies actual
Jacquet quotients with injections into the opposite induction. The orbit map
of a nonzero Jacquet map is nonzero by evaluation at one, hence injective
by source irreducibility. In the reverse direction, the published evaluation
adapter is surjective by target irreducibility.

The generic `semisimpleRetraction` constructs a retraction of an injection
into a semisimple representation on an independent carrier universe.
It uses Mathlib's module extension property after transporting intertwiners
to linear maps over the monoid algebra. Its result retains the actual
intertwiner and the equality of its composite with the injection to the
identity. `quotient_iff_summand` uses that constructor when semisimplicity
of the opposite induction is supplied explicitly. Applying the retraction
to equal images proves the converse injectivity.

These constructions are derived directly from the existing constructions,
not an additional literature statement. The field, source-carrier and
Levi-carrier universes are independent. It assumes only source smoothness,
with no admissibility, temperedness, square integrability or tensor
factorization; the occurrence consequences add the irreducibility and
semisimplicity hypotheses just stated. This pair neither upgrades a Jacquet
subquotient to a quotient, proves induced semisimplicity, nor compares upper
and opposite induction.
