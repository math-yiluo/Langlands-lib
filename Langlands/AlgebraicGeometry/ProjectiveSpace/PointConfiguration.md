# Fixed configurations of actual rational points

For every field `K`, natural number `n` and index type `I`,
`RationalPointHyperplaneBound n p q` bounds incidences of an indexed family
of actual rational-point morphisms with each nonzero linear form. Each
`p i` is an actual morphism `Spec K → ProjectiveSpace K n` over `Spec K`.
Incidence means membership of the corresponding homogeneous linear polynomial
in the homogeneous prime at the image of the unique point of `Spec K`.

The count is `Nat.card` of the subtype of incident indices. It counts repeated
entries by their indices. It uses the actual projective coordinate ring and
actual scheme points, without an algebraic-closedness hypothesis or a
surjectivity premise for a point comparison.

## Comparison with the vector-space incidence bound

`rationalPointHyperplaneBound_iff` identifies this bound with the published
`HyperplaneBound` on the representatives of the coordinate lines
`pointLineEmbedding n (p i)`. The proof substitutes the exact degree-one
incidence equivalence for each index and each functional. This comparison
does not require a finite index type; both sides use `Nat.card`.

## Scalarity from fixed actual morphisms

For a finite index type, `scalar_of_fixes_rationalPointConfiguration` assumes
that bound, the strict inequality

```
(n + 1) * q < Fintype.card I,
```

and an actual linear equivalence `e` satisfying
`(p i).1 ≫ linearAction K n e = (p i).1` for every `i`. It concludes that
`e.toLinearMap = a • LinearMap.id` for some `a : K`.

The point-action comparison transfers the equalities of actual morphisms to
fixed coordinate lines. The projectivization map formula and equality
criterion for two nonzero representatives show that each representative is
sent to a scalar multiple of itself. The coordinate space has dimension
`n + 1 > 0`, so the strict count inequality is precisely the dimension
inequality in the published finite-configuration scalarity theorem. Applying
that theorem gives the result.

`unit_scalar_of_fixes_rationalPointConfiguration` strengthens the conclusion
to a unit `a : Kˣ` with `e = LinearEquiv.smulOfUnit a`. If the scalar were
zero, the linear equivalence would send the nonzero constant-one coordinate
vector to zero, contradicting injectivity. The resulting nonzero field element
defines the unit, and equality of the underlying linear maps gives equality
of linear equivalences.

`linearAction_eq_id_of_fixes_rationalPointConfiguration` combines that unit
scalar conclusion with the actual scheme identity `linearAction_smulOfUnit`.
Its conclusion is equality with the identity scheme morphism, including the
structure-sheaf map, under exactly the same incidence, size and fixedness
hypotheses.

## Transfer to an embedded scheme

`eq_id_of_fixes_embedded_rationalPointConfiguration` applies to a scheme `X`
over `Spec K`, a monomorphism `i : X → ProjectiveSpace K n` over that base,
and indexed rational points of `X` over `Spec K`. It assumes the same
hyperplane and size bounds for their images. If an endomorphism `f` fixes
these points and satisfies the actual equivariance equation
`f ≫ i = i ≫ linearAction K n e`, then `f = 𝟙 X`.

Associativity and equivariance show that the linear action fixes each image
point. The preceding theorem makes that action the identity. Cancelling the
monomorphism `i` then gives equality of the original scheme endomorphisms.
An immersion supplies such a monomorphism, but no immersion construction or
existence of the equivariant lift `e` is asserted here.

## Provenance and scope

This is an internal adapter from the actual projective-space incidence and
action APIs to `FiniteConfiguration.HyperplaneBound.scalar_of_preserves_lines`.
The latter supplies the spanning, basis and full-support vector argument.
This module proves the comparison and scalarity under the incidence and size
hypotheses and transfers the resulting identity through an equivariant
monomorphism. It does not prove those hypotheses for torsion configurations,
identify arbitrary scheme morphisms from their rational points, or prove
the main ordinary moduli representability statement.
