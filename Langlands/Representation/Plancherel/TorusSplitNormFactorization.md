# Positive-power split-part and norm-kernel factorization

Worker 1374.

Let `T` be an affine torus locally of finite type over a nonarchimedean local
field `F : Type u`, in either characteristic. Let `i : A → T` be any actual
maximal split subtorus. The definition `splitNormExponent i` is the index of
the image of restriction from the rational characters of `T` to those of `A`.
This natural number is strictly positive and depends on the inclusion, not on
the rational point being factored.

For every `x ∈ T(F)`, `exists_split_mul_commonNormKernel` proves that there are
actual points `a ∈ A(F)` and `z ∈ rationalCommonNormKernel T` such that

```text
x ^ splitNormExponent i = rationalPoints.map i a * z.
```

The definition `splitNormFactorization` chooses such a pair together with its
product equality. The kernel point is a member of the existing subgroup
cut out by all normalized absolute values of rational algebraic characters.
The construction does not choose a splitting field or assume rational-point
surjectivity of an isogeny.

## Implemented derivation

This is an internal consequence of published Library results, with no new
literature assertion. Commutativity makes the split subtorus central. The
published `CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict`
therefore proves that the restriction image has finite index, hence that its
index is positive. This argument only needs a closed split subtorus, as stated
in `splitNormExponent_pos`.

For the factorization, the published
`IsMaximalSplitTorus.characterRestrict_injective_of_isTorus` detects rational
characters on the split part. The published
`RenardCartan.pow_index_mem_splitValuationImage` then puts the exponent-th
power of the valuation of `x` in the image of actual split-torus points.
Its witness `a` has the same valuation as `x` to that power. The point
`z = (i(a))⁻¹ * x ^ splitNormExponent i` consequently has zero valuation,
so `rationalCharacterValuation_ker` puts it in the common norm kernel.
Cancellation gives the displayed product.

## Scope for derived-point annihilation

This result is algebraic factorization on actual local-field points. It
proves no compactness assertion for a general torus. Applying it within a
torus contained in an actual algebraic derived subgroup keeps both factors
in that subgroup. A reduction for all derived points still requires the
positive-power torus/additive factorization, compactness of the general
torus norm kernel, and the remaining root-reflection input. This helper
does not prove the unrestricted ambient smooth-real annihilation target.
