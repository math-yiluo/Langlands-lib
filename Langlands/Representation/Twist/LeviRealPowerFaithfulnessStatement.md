# Faithful real determinant exponents on product Levis

`Langlands.LeviRealPowerFaithfulnessStatement.{uF}` is a proposition about every
p-adic field `F : PadicField.{uF} p`, each compatible `F.TopologicalData`, and
every ordered positive block shape `B` of any rank `n`.

The character `T.leviRealPowerCharacter B t` is the product of the actual block
determinant characters with real exponent vector `t`. The statement has three
conclusions:

1. Evaluate the character at the block-scalar element with the chosen
   uniformizer in block `i` and unit scalar `1` in every other block. Its
   complex value is the real number
   `q ^ (-(B.size i : ℝ) * t i)`, embedded in `ℂ`, where
   `q = T.residueCardinality`.
2. The map from real vectors to characters restricted along
   `B.blockScalarLevi F.Carrier` is injective.
3. The map from real vectors to characters on the full product Levi is
   injective.

Here restriction is composition of actual monoid homomorphisms. Thus either
restricted-character equality or full-character equality is equivalent to
equality of the real exponent vectors. The tested element is scalar on an
entire block; its determinant has the block-size power, which accounts for the
factor `B.size i`.

There is no sum-zero, noncentral, chamber, multiple-block, or positive-rank
hypothesis. In particular, the one-block central direction is retained. The
rank-zero case is included; its block index set is empty, so evaluation is
vacuous and the real-vector space has only one element.

## Provenance and status

This is a derived statement from the published real-character normalization
and the specified uniformizer, rather than a quotation of an external result.
`coe_leviRealPowerCharacter_blockScalar` supplies the block-size weights, and
`uniformizerUnit_zpow_abs` gives the normalization `|ϖ| = q⁻¹`.
The expected elementary proof evaluates one block at a time and uses
injectivity of `r ↦ q^r` for `q > 1`, followed by cancellation of the positive
block size. Full-character injectivity then follows by restriction.

This file declares the proposition only. Its proof requires a separate
exact-target theorem and independent review. It neither recovers tempered
inducing representations nor asserts semistandard conjugacy.
