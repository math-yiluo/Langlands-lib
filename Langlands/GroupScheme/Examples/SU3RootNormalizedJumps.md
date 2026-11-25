# Indivisible jumps for base-normalized quadratic valuations

This is an internal derivation from the coordinate jump parity
results and the published quadratic conjugation and valuation arithmetic.
Let `L/K` be a separable quadratic extension, in independent universes.
`IsNormalizedQuadraticValuation K L ω` requires that the additive valuation
`ω : L → WithTop ℝ` is invariant under conjugation, every nonzero embedded
`K` scalar has an integer value, and some embedded `K` scalar has value one.

The quadratic norm `x σ(x)` lies in the embedded base field and is nonzero for
nonzero `x`. Its value is twice that of `x`, so all nonzero extension values are
half-integers. This repeats the norm argument of the existing ramified
half-integer lemma without assuming an attained half value.

If all these values are integers, the integer branch of `SU3RootJumpParity`
supplies an indivisible central jump. Otherwise a nonintegral value is `n/2`
with `n` odd. Multiply its element by the base value-one scalar raised to
`-(n / 2)`, where `/` is integer Euclidean division. The resulting value is
`1/2`. This gives the precise `IsRamifiedQuadraticValuation` hypotheses, so the
ramified branch supplies an indivisible central jump.

Thus `hasIndivisibleCentralJump` proves that a real central coordinate jump
exists whose half is absent from the ordinary quotient jump set. No
characteristic, residue characteristic or residue-perfection restriction is
imposed. Normalization over a finite henselian field tower is done in
`SU3RootTowerJumps`; comparison with actual affine roots is not part of this
module.
