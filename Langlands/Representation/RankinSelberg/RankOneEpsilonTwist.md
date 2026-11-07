# Rank-one determinant twists of the full epsilon certificate

Authors: Worker 357, adapting the published rank-one gamma transport of
Worker 458 and its statement interface of Worker 1062.

`RankOneEpsilonTwistStatement.{uF,uV}` asserts that the existing p-adic
JPSS epsilon relation for `(π ⊗ χ∘det, 1)` is equivalent to the relation
for `(π, χ)`, with the same coefficient unit and integer exponent.
Both representations have rank one. The theorem `rankOneEpsilonTwist`
proves this proposition. The field and the carrier of `π` have independent
universes, the prime and p-adic field are arbitrary, and the p-adic relation
uses the field's canonical topological data.

The additive character is continuous, nontrivial and unit-circle-valued,
as required by `UnitaryAdditiveCharacter`. The additive Haar measure is
arbitrary. The character `χ : Fˣ →* ℂˣ` need not be continuous. No
smoothness, irreducibility, Whittaker-type, finite-dimensionality or
self-duality premise is used for this transport. The assertion transports
a supplied certificate in either direction and does not itself assert
epsilon-factor existence.

The fixed-functional proof reuses the actual coefficient and integral
identities from `RankOneGammaTwistIntegrals` and the equality of forward
rational-value families from `RankOneGammaTwistEquations`. Surjectivity of
the actual coefficient maps proves equality of the dual rational-value
families as well. Consequently both normalized generator conditions
transport with the same original and dual polynomials.

For every pair of coefficient-model vectors and every row test, the
forward and dual integrals agree after moving the character between the
two members. The same Fourier partner and rational continuations therefore
work in both equations. The minus-one scalar of the test is `1` for the
trivial character and `χ(-1)` for the character test. Its exponent in the
rank-one normalized functional equation is zero, so the coefficient and
integer exponent of the epsilon monomial remain unchanged.

The proof then transports the complete relation. It preserves
compatible quotient-measure existence, carries nonzero functionals
through twisting while keeping their underlying linear forms, and applies
the fixed-functional comparison for every compatible quotient measure and
every nonzero functional pair. It selects the equal-rank branch of the
existing pair relation and installs the canonical p-adic structures.
Neither the existence clauses nor the universal clauses are dropped.

`isPadicPairEpsilonFactor_rankOneCharacters_mul` specializes the result:
the full epsilon relation for the character pair `(χ,η)` is equivalent to
that for `(χ*η,1)`. Its proof identifies the determinant twist of the first
character representation with the product-character representation.

This is an internal derivation from the published integral identities
and epsilon definitions. It introduces no new epsilon factor, analytic
assumption or external literature assertion. It supplies the automorphic
character-product reduction for a future rank-one comparison. Equality
with the explicit abelian Gauss-integral epsilon expression, reciprocity
existence and the closed all-field correspondence remain separate
obligations.
