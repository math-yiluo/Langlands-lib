# Nonvanishing in a simple-root string of length one

For an arbitrary field `k : Type u`, let `G` be the actual affine group scheme with supplied split pinning `p`. Let `ρ` be a finite matrix representation, let `lam` satisfy `p.IsHighestWeight ρ lam`, and let `a` be a supplied simple root whose integral coroot pairing with `lam` is one. For every supplied normalized root parametrization `x`, every supplied simple-reflection representative `s`, and every nonzero vector `v` in the actual `lam` weight space, the theorem
`SplitPinning.NormalizedRootParametrization.coefficientMatrix_one_reflected_ne_zero`
proves

```text
coefficientMatrix (ρ.restrict x.hom) 1 *ᵥ
  ((ρ.rationalMatrix s.point) *ᵥ v) ≠ 0.
```

The coefficient is that of the universal polynomial matrix of the actual root-group representation. The weight spaces use the universal torus action, so the assertion does not replace scheme weights by eigencharacters on rational torus points. It imposes no algebraic closedness, characteristic, infinitude, perfectness or simple-connectedness hypothesis. It does not prescribe the resulting nonzero scalar. The full `IsHighestWeight` package remains a hypothesis; this proof uses its cone bound and does not construct such a representation.

`SplitSimpleRootHighestCoefficientArbitraryFieldStatement` records the assertion for representations on `Fin d`, over every field in the chosen universe. The theorem `splitSimpleRootHighestCoefficientArbitraryField` proves this proposition by applying the preceding result, which also allows an arbitrary finite matrix index type.

## Implemented proof

`SplitPinning.neg_nsmul_simpleRoot_not_mem_positiveRootMonoid` expresses membership in the nonnegative simple-root cone by natural coefficients. Integral linear independence of the simple roots contradicts a negative coefficient at `a`. Consequently, `IsHighestWeight.weightSpace_add_nsmul_simpleRoot_eq_bot` shows that every weight `lam + m alpha` with `m > 0` is absent, where `alpha` is the root at `a`.

The published coefficient-weight transport then shows that every positive-degree root coefficient annihilates `v`. The supplied representative carries `v` to a vector `w` of weight `reflection_a lam = lam - alpha`. Thus every root coefficient of degree at least two annihilates `w`. This is `dividedPower_reflected_eq_zero_of_one_lt`.

The finite polynomial expansion of an actual additive-group representation implies that a vector annihilated by all positive-degree coefficients is fixed over every affine algebra. The lemma `affinePoint_eq_constantPoint_rationalPoint` compares ordinary affine coordinates with constant rational root points using naturality of `ΓSpecIso`. Because the supplied parametrization represents the whole intrinsic root subgroup, `rationalMatrix_mulVec_eq_self_of_dividedPower_eq_zero` gives fixity under every rational point of that subgroup.

Suppose the selected degree-one coefficient annihilates `w`. All positive-degree coefficients then annihilate both `v` and `w`, so the positive root subgroup fixes both. Conjugation by `s` carries the negative root subgroup to the positive one. Applying the representation and cancelling the invertible matrix of `s` shows that the negative root subgroup fixes `v`. This argument is implemented in `rationalMatrix_negRoot_mulVec_eq_self_of_root_fixed_reflection`.

The existing canonical representative attached to `x` is the product of a negative-root point, the positive-root point `x(1)`, and another negative-root point. Hence it fixes `v`. Its normalizer action also carries `v` into the reflected weight space. These weights are distinct because the root is nonzero in the integral character lattice. Applying the universal character projector to the two memberships makes `v` both its own projection and zero, contradicting `v ≠ 0`. This proves the stated nonvanishing.

## Provenance and scope

This is an internal derivation from the published actual-root coefficient, normalizer, conjugation and canonical opposite-factor interfaces. It uses the finite polynomial expansion in `SteinbergPolynomialAction`; no derivative determines an additive action in positive characteristic, and no factorial is inverted. The argument above is the implemented proof route and has no additional external source assertion.

Worker 1284 isolated the local pairing-one input in `SimpleRootHighestCoefficient`. Worker 1317 developed and implemented this arbitrary-field proof and its supporting lemmas. This supporting unit does not import or modify that statement pair. Its stronger theorem implies the local algebraically closed version by specialization. It proves no existence theorem for highest-weight representations, no simple-connectedness ascent theorem and no final split Steinberg quotient isomorphism.
