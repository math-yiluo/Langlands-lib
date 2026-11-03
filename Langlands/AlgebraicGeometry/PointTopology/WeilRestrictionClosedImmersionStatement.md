# Closed-immersion preservation by finite-type affine Weil restriction

This proposition records the preservation assertion used in Conrad, *Weil
and Grothendieck approaches to adelic points* (December 31, 2011),
Example 2.4, printed page 3. It uses the actual representing algebras and
actual scheme maps of `FiniteType.lean`, `Functorial.lean` and
`AffineWeilRestrictionMaps.lean`.

For arbitrary commutative rings `A` and `B`, with `B` a finite projective
`A`-algebra, `WeilRestrictionClosedImmersionProperties A B` is the
conjunction of two assertions:

1. Every surjective `B`-algebra map between finite-type commutative
   `B`-algebras induces a surjective map between their constructed
   finite-type Weil-restriction algebras.
2. Every closed immersion between actual affine finite-type schemes over
   `Spec B` induces a closed immersion between their constructed actual
   affine Weil-restriction schemes over `Spec A`.

Both original schemes are objects of `Over (Spec B)`. Their affineness
makes the specified locally finite-type structure morphisms full finite
type. The conclusion uses the actual map `affineWeilRestrictionMap`,
whose point comparisons are already constructed; it does not quantify
over an assumed map with desirable properties.

Conrad assumes a module-finite locally free ring extension for the whole
example. This algebraic preservation statement uses the finite-projective
algebra hypothesis and does not require faithfulness. The same
universal-property argument applies without injectivity of `A → B`,
since the needed tensor injectivity follows from flatness of the
projective `A`-module `B`. This broader algebraic scope is a derived
extension of the cited preservation assertion. It makes no assertion
about the coefficient map being a topological embedding.

There are no topological-ring, Hausdorff, local-ring, open-unit, field,
Noetherian or finite-presentation hypotheses. The proposition is a target,
not a proof. The point homeomorphism and representation on all test
schemes are separate obligations.
