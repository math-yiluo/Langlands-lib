# The full actual rank-one conclusion from opposite-pair existence

This internal derived unit isolates the remaining geometric obligation in
the actual rank-one factorization proof. `HasOppositeFactorPairs` says only
that every nonidentity rational point of every actual relative root
subgroup has an ordered opposite pair whose product normalizes the given
torus. It asserts neither uniqueness nor any reflection or equal-factor
identity.

For a supplied pair at a nonzero character `n • a`, its actual integral
coroot pairs with that character to give two. Bilinearity expresses this
as `2 = n * ⟨a, ν⟩` in the integers. Consequently the natural multiplier
divides two and equals one or two. This argument does not require `a`
itself to be a root.

For a smooth affine group over an arbitrary field with a split subtorus,
the preceding unconditional rational-point theorem supplies a nonidentity
point in any actual root `n • a`. The existence-only predicate supplies
its pair, so the integral argument bounds every root multiple without
assuming a relative-root system. If the double is absent, this bound
excludes all second and higher positive roots.

For any supplied pair at `a`, the proved Weyl action sends `a` to `-a`
and preserves the actual root set. Applying that action to a hypothetical
higher root on the negative ray gives the forbidden higher positive root.
This supplies the absence condition on both rays from the single
nonmultipliable-root hypothesis in the published target.

The final assembly applies the existing automatic uniqueness, factor
nonidentity, and reflection theorems to each pair. Under the absence of
the double, the two higher-root exclusions allow the proved fpqc inversion
argument to give equality of the factors, the stated conjugation identity,
and membership of the product's square in the actual image of the rational
torus points. The result is exactly `HasRankOneFactorization i` with
`HasOppositeFactorPairs i` retained as a premise. The converse simply
forgets the extra conclusions, yielding the stated equivalence.

All results have arbitrary universe and field. Their provenance is internal
composition of the imported actual root, coroot, rational-point and fpqc
inversion proofs. This unit does not prove opposite-pair existence or claim
the unconditional `RootRankOneFactorizationStatement`.
