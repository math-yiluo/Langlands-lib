# Relative invariants obtained from absolute invariants

Author: Worker 80.

This derived construction composes a supplied additive equivalence
`invK : absoluteCohomology K 2 ≃+ RationalModIntegers` with the actual
`closureInflation K E 2`. Its resulting additive homomorphism is
`relativeInvariantFromAbsolute K E invK` on the existing ordinary
relative degree-two cohomology. Here `K` is any field in universe `u`,
and `E` is a finite normal intermediate field of its algebraic closure.
No cohomology object or comparison map is changed.

The application lemma exposes this composition. The injectivity lemma
uses an explicit hypothesis that closure inflation is injective, then
composes that injectivity with the injectivity of `invK`.

The range lemma assumes an additive equivalence `invE` for the actual
absolute cohomology of `E`, exactness in the form

`range (closureInflation K E 2) = ker (absoluteRestriction K E 2)`,

and the degree law

`invE (absoluteRestriction K E 2 x) = [E:K] • invK x`.

Restriction uses the specified `K`-compatible embedding of algebraic
closures, with exactly the algebra and scalar-tower hypotheses of the
existing map. From these inputs the lemma proves that the relative
invariant's range equals `denominatorSubgroup [E:K]` in the actual
rational quotient.

For the forward inclusion, an inflated class lies in the restriction
kernel by exactness. Applying the degree law shows that its invariant
is annihilated by the degree. For the reverse inclusion, lift an element
annihilated by the degree through `invK.symm`. Its restriction has zero
`invE` value by the degree law, and is therefore zero by injectivity of
`invE`. Exactness then supplies a relative preimage; applying `invK`
gives the original element. The range proof does not require inflation
injectivity, which is used only by the separate injectivity lemma.

## Provenance and scope

This is an internal elementary deduction from the definitions of
homomorphism range and kernel, additive equivalence, and the imported
`denominatorSubgroup`. The proof above is the implemented argument;
no external arithmetic result is invoked. The actual inflation already
includes the inverse of the proved finite continuous-to-ordinary
comparison from `FiniteComparison`.

The supplied absolute equivalences, inflation exactness, and degree law
are hypotheses of this construction's property lemmas, not conclusions
or new axioms. This module proves neither their existence nor
`CohomologyExistence`. In particular it does not discharge the arithmetic
absolute invariant construction. It treats finite normal intermediate
fields in the common universe `u`; transporting arbitrary extension
carriers in independent universes is separate work.
