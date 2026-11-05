# Original field and integer points of the number-field S-integer Weil model

This derived construction proves local field comparisons and their integral
compatibility for the actual global S-integer Weil model in Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed page 10.

Let A be the actual lower S-integer ring for any finite set S of original
finite places, and B the actual upper S-integer ring for its full preimage.
Let Y be a locally finite type B-scheme equipped with an actual relative
projective immersion.
`numberFieldSIntegerModelFieldPointHomeomorph` identifies completed-field
points of the actual relative Weil restriction over A with the product of
Y's points over every original upper completion above the chosen finite
lower place.
`numberFieldSIntegerModelInfinitePointHomeomorph` supplies the corresponding
homeomorphism at every original infinite place, including real and complex
places. Neither field comparison requires the chosen place to be outside S.

The existing `schemePointTopology` is used on every point space. The
homeomorphisms specialize the proved projective-immersion completed-tensor
Weil comparison using `SIntegerCompletedFieldTensor`. Finite-dimensionality
over the complete nontrivially normed lower field proves that each original
upper completion has its finite-module topology. At infinite places the
existing original completion norm is used. The projective immersion supplies
the separatedness and finite affine neighborhoods needed by the general
comparison, so nonaffine models are included. The counit identities prove
that every component is the original relative Weil counit along the actual
completed-field factor test spectrum.

At a finite place outside S, the original completed valuation rings also give
the integral local homeomorphism proved in
`NumberFieldSIntegerWeilIntegralTopology`.
`numberFieldSIntegerModelFieldPointHomeomorph_integralToField` proves that
extending an integral model point to the field commutes with the two
homeomorphisms at every original upper place. Its proof applies the general
completed-tensor counit naturality theorem to the original inclusions of the
completed integer rings into their completed fields. The coefficient square
commutes by the explicit scalar towers and original completion embeddings.

The integral-image equivalence then proves that a field point of the actual
lower Weil model comes from an integral point if and only if each upper
component comes from an integral Y-point. In one direction use the commuting
square. Conversely choose integral preimages for the upper components, apply
the inverse integral homeomorphism, and use injectivity of the field
homeomorphism together with the same square. This concerns existence of
actual integral model points; it assumes no image characterization.

K and L are number fields in an arbitrary common universe, with the given
original field embedding. An empty finite-place S is allowed. The
outside-S `Fact` premise occurs only in the integral compatibility and
integral-image clauses. Y has its stated immersion; its existence for
original quasi-projective field schemes is proved separately. The finite-level
adelic product and full adelic Weil homeomorphism remain host obligations.
