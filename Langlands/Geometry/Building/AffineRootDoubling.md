# Ordinary representatives of extended affine roots

For `D : KPApartmentData i ω`, suppose that every relative root `a` satisfies
`4 • a ∉ relativeRoots i`. The construction
`KPApartmentData.ordinaryAffineRootForExtended` sends each extended affine root
`ψ` to an element of the existing set `D.affineRoots`. It returns `ψ` if that
functional is already an ordinary affine root, and `2 • ψ` otherwise.

The defining results prove that the returned root is either `ψ` or `2 • ψ`,
has the same sign at every apartment point, and has the same affine hyperplane.
The construction makes no additional uniqueness claim.

The theorem `mem_or_two_smul_mem_affineRoots_of_no_quadruple` gives the
underlying AS4 conclusion:

```text
ψ ∈ D.extendedAffineRoots →
  ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots.
```

The field and all group-scheme data have arbitrary universe `u`. The generic
result requires a commutative group scheme `S`, a monomorphism `i : S → G`
into an affine group scheme, the supplied apartment data, and the stated
absence of quadruple roots. It does not require smoothness or a split-torus
hypothesis.

For a smooth affine group scheme and a split torus `S`, the theorem
`no_quadruple_root_of_oppositePairs` obtains the root bound from the existing
existence-only predicate `RelativeRoot.HasOppositeFactorPairs i`. Consequently,
`mem_or_two_smul_mem_affineRoots_of_oppositePairs` proves the same AS4 conclusion
from this existence predicate and the supplied apartment data.

## Implemented proof

If the derivative `a` of a jump `ψ` has no doubled relative root, then
`doubleRootGroupPoints i a = ⊥`. Were `ψ` not ordinary, its weak affine root
group would be contained in the product of its strict group with this trivial
group. This would make the two filtration groups equal, contradicting the
extended-root jump. This proves `mem_affineRoots_of_not_double_root`.

The theorem `affineRootGroupPlus_double_le` extends the existing depth-zero
strict-filtration inclusion to any affine depth:

```text
U_(2ψ)+ ⊆ U_ψ+.
```

The derivative of `2ψ` is identified using the public theorem `rootForm_nsmul`.
At a chosen apartment point `x`, V4 says that the doubled-root valuation of
`g ∈ U_(2a)` is twice its `a`-valuation. The actual root-subgroup inclusion
`RelativeRoot.double_subgroup_le` puts `g` in `U_a`. If its `a`-valuation is
infinite, the required strict inequality is immediate; otherwise the inequality
`2ψ(x) < 2x_a(g)` reduces to `ψ(x) < x_a(g)` in the real numbers.

If `ψ` is a nonordinary jump, the published
`affineRootGroup_subset_mul_double_of_not_mem_affineRoots` factors every
`g ∈ U_ψ` as `v * w`, with `v ∈ U_ψ+` and `w ∈ U_(2ψ)`. If the doubled
filtration were not a jump, then `w ∈ U_(2ψ)+ ⊆ U_ψ+`, which would imply
`U_ψ = U_ψ+`. This is the contradiction established in
`affineRootGroupPlus_double_ne_of_not_mem_affineRoots`.

For the main theorem, a nonordinary `ψ` must therefore have derivative `a`
with `2a` a relative root and a doubled filtration jump. The hypothesis excludes
`2(2a) = 4a` from the relative roots, so the first lemma makes `2ψ` ordinary.
The conditional definition selects the resulting ordinary root. Its sign and
hyperplane properties follow from positivity and nonvanishing of the scalar `2`.

For the opposite-pair specialization, the published theorem
`RelativeRoot.HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem` applies to
any character whose `n`-fold multiple is a relative root. It uses an actual
opposite pair's integral coroot and rational nontriviality of the actual root
subgroup, and forces `n = 1` or `n = 2`. Taking `n = 4` supplies the root bound.
There is no relative-root-system premise in this specialization.

## Provenance and scope

This is an internal derivation from the existing apartment, root-subgroup,
half-wall factorization and actual opposite-pair constructions. It introduces
no new external source assertion. The names “ordinary” and “extended” refer
to the exact definitions `KPApartmentData.affineRoots` and
`KPApartmentData.extendedAffineRoots`; the proof checks their subgroup
conditions directly.

No full apartment-axiom package, AS5, local reflection-arrangement geometry, or
simply connected normalizer generation is assumed or established. Opposite-pair
existence remains an explicit premise of the actual-group specialization.
This unit does not prove `SimplyConnectedFacetFixingStatement`.
