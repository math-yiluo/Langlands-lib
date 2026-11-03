# Separation of a dynamic parabolic normalizer from opposite directions

Author: Worker 1297.

This internal unit proves that the opposite dynamic unipotent `U(-χ)`
intersects the all-test normalizer of `P(χ)` trivially. The base is `Spec R`
for any commutative ring `R`, the underlying scheme of `G` is affine, and
`χ : Gm → G` is any cocharacter. The test schemes are arbitrary, including
non-affine and nonreduced schemes. No field, smoothness, connectedness or
reductivity hypothesis is used.

## The universal commutator argument

The general lemma `Dynamic.eq_one_of_mem_normalizer_of_disjoint` works over
any base scheme. Let `A` be a subgroup functor normalized by the range of
`χ`, and suppose a point of both `A` and `P(χ)` is always the identity.
Then a point of both `A` and `N(P(χ))` is also the identity.

For a test scheme `T` and such a point `g`, work on `V = T × Gm`.
Write `n` for the pullback of `g` and `x = χ(t)` for the universal
cocharacter point. This point `x` belongs to `P(χ)` because the image of
a cocharacter centralizes that cocharacter. Normalization gives
`n⁻¹ x n x⁻¹ ∈ P(χ)`. The normalization of `A` by `χ` also puts this
commutator in `A`, so it is the identity. It follows that
`x n x⁻¹ = n`: the orbit of `g` is constant. Thus `g` belongs to
`Z(χ)`, hence to `P(χ)`, and the assumed intersection makes `g` trivial.
The use of the universal cocharacter point, over the full scheme `V`,
retains the all-test meaning of the normalizer.

For `A = U(-χ)`, normalization follows from the published
common-commutative-group cocharacter normalization lemma in
`Dynamic.OppositeCellContraction`. Triviality of `U(-χ) ∩ P(χ)` is the
published theorem in `Dynamic.OppositeIntersection`. This gives
`eq_one_of_mem_opposite_unipotent_of_mem_normalizer` and its equality of
subgroup functors `opposite_unipotent_inf_normalizer_parabolic`.
The definition `oppositeUnipotentNormalizerEquivBot` realizes this equality
on each test scheme as a multiplicative equivalence from the intersection
subgroup to the trivial subgroup. It is the identity on underlying points,
with membership transported along the proved subgroup equality.

Finally, `mem_parabolic_of_mem_normalizer_of_opposite_factorization`
assumes a factorization `g = u p`, with `u ∈ U(-χ)` and `p ∈ P(χ)`.
If `g` normalizes `P(χ)`, so does `u = g p⁻¹`. The separation theorem
forces `u = 1`, and hence `g ∈ P(χ)`.

## Provenance and remaining scope

The proof is an internal consequence of the published dynamic subgroup
definitions, their common-cocharacter normalization, the opposite
intersection theorem, and the definition of the all-test normalizer.
It does not invoke an external structural theorem.

This unit supplies a local separation step toward scheme-theoretic
parabolic self-normalization. It does not construct an opposite open
cell, prove that arbitrary normalizer points have the displayed
factorization, identify every geometric parabolic with a dynamic
parabolic, or prove the full `ParabolicSelfNormalizerStatement`.
