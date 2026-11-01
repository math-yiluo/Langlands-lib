# Linear intertwiner transport and natural determinant quotient comparisons

Author: Worker 2. This internal construction extends the actual finite-order
determinant transport on `OperatorSubquotient`. The number field has arbitrary
universe, the rank is any natural number and coefficients are complex.
The character has an explicit finite-order proof. No CM-field hypothesis is
imposed. The Hom spaces here consist of complex-linear maps intertwining every
element of the concrete automorphic operator algebra on the actual module
quotients.

Write `Dχ,Q` for the existing induced quotient linear equivalence and `Cχ` for
the existing automorphism of the concrete operator algebra. For an arbitrary
whole-action map `L` between the twisted quotients,
`Intertwiner.determinantUntwist` has the actual underlying linear map
`Dχ,T⁻¹ ∘ L ∘ Dχ,Q`. To prove its intertwining identity at any original operator
`a`, surjectivity of `Cχ` writes `a = Cχ(b)`. Injectivity of `Dχ,T`, the two
quotient covariance identities and the supplied intertwining identity at `b`
then prove the required identity. Thus inverse transport is constructed for
every twisted intertwiner; it is not an additional preservation premise.
The covariance proof is first established for abstract representations and
linear equivalences with a common surjective operator parameter map, then
instantiated with the concrete quotient actions and `Cχ`. The application
formula specifies the resulting map on every vector.

Cancellation of the actual source and target quotient equivalences proves
that untwisting after twisting and twisting after untwisting both return the
original intertwiner. `Intertwiner.determinantTwistLinearEquiv` bundles this
pair as a complex-linear equivalence of the entire intertwiner spaces.
Its forward map is exactly the previous determinant transport and its inverse
is the newly constructed inverse conjugation. Linearity follows pointwise from
linearity of the actual target quotient equivalence. Bijectivity, equality
reflection, preservation of zero and reflection of zero follow from this
linear equivalence.

`Intertwiner.determinantTwist_one_naturality` says that twisting a supplied map
by the unit character and composing with the source unit comparison equals
composing the original map with the target unit comparison.
`determinantTwist_mul_naturality` compares two maps from the product-character
quotient of the source to the successive-twist quotient of the target.
The first applies the source product comparison and then twists the supplied
map successively; the second twists the map by the product character and then
applies the target product comparison. The universal-quantifier equivalence for surjectivity of the actual source
product quotient map reduces the identity to an original vector, without
substituting through dependent quotient types. Explicit congruence and
transitivity compose the exact source product-comparison formula, the two
successive transported-map formulas, the inverse target product-comparison
formula and the inverse product-transported-map formula. These identities compare actual maps between
dependent quotient presentations.

The corresponding `Equivalence.determinantTwist_one_naturality` and
`Equivalence.determinantTwist_mul_naturality` identify the two composites as
genuine whole-action representation equivalences, with the same pointwise
proofs.

Provenance is internal: the actual quotient maps and covariance in
`OperatorSubquotientDeterminantTwist`, actual map transport in
`OperatorSubquotientDeterminantTwistClasses`, actual unit/product comparisons
in `OperatorSubquotientDeterminantAction`, the surjective concrete algebra
automorphism from `DeterminantOperatorConjugation` and Mathlib's genuine
intertwiners and linear equivalences. No new original-literature
identification is claimed.

The construction supplies algebraic Hom-space transport and these naturality
identities. It supplies no quotient evaluation or topology, continuity of
arbitrary intertwiners, tensor-factor selection, general coherence theorem,
central-character or cusp predicate on arbitrary quotients, or nonzero,
irreducible or spectral existence assertion.
