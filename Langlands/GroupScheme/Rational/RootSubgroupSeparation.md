# Actual opposite-root multiplication and factor-pair separation

This module constructs `RelativeRoot.oppositeMultiplicationEmbedding`.
For an affine group scheme over any field, a split torus mapping into the
group, a nonzero character `a`, and any test scheme `U`, it embeds
the product of the actual `a` and `-a` subgroup-functor point sets into
the ambient group points by `(x, y) ↦ x * y`. No represented root
subgroup, reductivity, maximality, or relative-root membership is assumed.

The construction uses all-test opposite-root separation. The proof chooses
a cocharacter pairing positively with `a` using the published split-torus
lattice theorem. The existing orbit pullback lemma puts the root subgroups
into opposite dynamic unipotent groups. The published opposite-unipotent
and parabolic intersection theorem makes their intersection trivial.
If `x * y = x' * y'`, the common point `x'⁻¹ * x = y' * y⁻¹`
belongs to both root subgroups. It is the identity, which proves the
injectivity required by the embedding.

The module also proves separation from a negative dynamic parabolic:
if a cocharacter pairs positively with `a`, an `a`-root point admitting
a limit along its negative is the identity. This version needs the
positive pairing but does not require splitness.

The theorem `normalizer_eq_one_of_mul_opposite` shows that any rational
normalizer point which is a product of an `a`-root point and a `-a`-root
point is the identity. It applies the published
`normalizer_eq_one_of_unipotent_product` from
`BruhatOppositeCellReduction` after putting the two root points into
opposite dynamic unipotent groups. No Weyl-action premise or monomorphism
assumption on the torus map is used in this theorem.

`IsOppositeFactorPair.factors_ne_one` proves that both factors of any
actual normalizing opposite pair for a nonidentity root point are
nonidentity. If either factor were the identity, the product would be a
normalizer in a product of opposite root groups and hence the identity.
The middle point would then belong to both root groups, contradicting
its nonidentity. This result also needs no monomorphism assumption.

The remaining results assume the torus map is a monomorphism.
A root-flipping normalizer cannot itself belong to the root subgroup:
conjugating that point by itself places it in the opposite subgroup.
Separation would make the normalizer the identity, whose Weyl action
cannot negate a nonzero character. The module also proves the resulting
two-factor obstruction and a version of factor nonidentity which assumes
the product flips the character, without assuming the middle point is
nonidentity.

Finally, `IsOppositeFactorPair.eq_of_flip` compares arbitrary opposite
pairs `p` and `q` for the same middle point `x`. It assumes only that
the first product negates `a`; it needs no premise comparing Weyl classes
and no membership or nonidentity assumption on `x`. Put

```
n = p₁ x p₂,   m = q₁ x q₂,
v = q₁ p₁⁻¹,  w = p₂⁻¹ q₂.
```

Both `v` and `w` belong to the negative root subgroup. Conjugation by
`n⁻¹` puts `n⁻¹ v n` in the positive root subgroup. The identity
`n⁻¹ m = (n⁻¹ v n) w` and the normalizer separation theorem give
`n⁻¹ m = 1`. Opposite-root separation then forces `n⁻¹ v n = 1`
and `w = 1`. Thus `v = 1` and the two pairs agree.

These constructions and proofs are internal deductions from published
orbit, conjugation, split-torus lattice, and dynamic-subgroup results.
They establish neither existence of normalizing opposite pairs nor
their reflection action, and they do not prove the nonmultipliable-root
conclusions. The full `RootRankOneFactorizationStatement` remains open.
