# Root points lie in every character-valuation kernel

Let `S` be a split torus over a field `k`, let `i : S → G` be any group-scheme
map, and let `a` be any nonzero character of `S`. For any valuation `v` of
`k` with values in a linearly ordered commutative group with zero,
`rootGroupPoints_le_characterValuationKernel` proves that the rational points
of the intrinsic root functor lie in `characterValuationKernel v G`.
The field and schemes use arbitrary universe `u`; the value group is unrestricted.

The proof applies the all-test rational-character vanishing theorem from
`Rational.RootCharacterKernel` at `Spec k`. It then transports evaluation
through the existing `Γ(Spec k) ≅ k` isomorphism and applies `v(1) = 1`.
No smoothness, reductivity or maximality hypothesis is used.

For any subgroup `H` of `G(k)`, the second lemma consequently proves
`U_a(k) ∩ (characterValuationKernel v G ∩ H) = U_a(k) ∩ H`.
In the integral-model application, `H` is the pointwise fixer and the first
intersection is the full-model subgroup. This simplification does not identify
the remaining root/fixer intersection with a valuation filtration.

This is internal derived content from full intrinsic root-character vanishing
and the existing definitions of root points and character-valuation kernels.
