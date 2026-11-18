# Algebraization on finite affine splitting tests

This internal construction supplies the finite-algebra part of finite étale
descent for the adic Hom comparison. It uses the Library's globally split
comparison as an explicit hypothesis. The final finite étale descent theorem
is assembled separately.

Let `A` be a noetherian commutative ring, complete and separated for an ideal
`I`. Let `H` and `G` be actual group schemes over `Spec A`, with `G` affine over
the base. Suppose `φ : A →+* B` is finite and the pullback of `H` to `Spec B` is
diagonalizable. Given `DiagonalizableAdicHomComparisonStatement`,
`finiteAffineAlgebraization` assigns to an actual compatible adic system `s` a
homomorphism between the pullbacks of `H` and `G` to `Spec B`.

The construction has `s.IsAlgebraization` in the sense defined in
`AdicAlgebraization`: after any further test over `Spec B` whose map to `Spec A`
factors through `Spec A/I^(n+1)`, it agrees with evaluation of the `n`th member
of `s`. The actual family with this property is unique. No étaleness or
surjectivity assumption on `φ` is used in this module.

The implemented proof has three parts:

1. `isAlgebraization_of_restrict_pull` starts with a homomorphism whose
   restrictions over `B/(I.map φ)^(n+1)` equal `System.pull φ s`. Flattening
   identifies this equality with the prescribed evaluation over the original
   quotient of `A`. The Cartesian quotient square from
   `isPullback_quotientSpecMap` factors every further test through the quotient
   of `B`. Evaluation along this factorization gives all identities in
   `IsAlgebraization`. This lemma does not need finiteness or completeness.
2. `eq_of_isAlgebraization_of_injective` uses injectivity of restriction over
   `B` to compare two algebraizations. Their all-test properties agree on the
   quotients of `B`; the flattening equivalence identifies these identities
   with equality of their actual quotient homomorphisms. This general lemma
   likewise needs only the stated injectivity hypothesis.
3. `restrict_bijective_finite_affine` equips `B` with the algebra structure of
   `φ`. Finite algebras over a noetherian ring are noetherian, and the published
   finite-module completeness theorem gives completeness of `B` for `I`.
   `IsAdicComplete.map_algebraMap_iff` converts this to completeness for the
   image ideal. Affineness of the target survives pullback. The split
   comparison therefore gives bijectivity of restriction over `B`.

`exists_isAlgebraization_affine` applies that bijectivity to `System.pull φ s`
and then uses the first lemma. `eq_of_isAlgebraization_affine` applies its
injectivity through the second lemma. `finiteAffineAlgebraization` chooses the
resulting homomorphism, and `isAlgebraization_finiteAffineAlgebraization` records
its property. Uniqueness ensures the chosen result is independent of the
existence witness.

The provenance is internal and derived: the construction combines the supplied
split comparison with the Library's actual adic-system, pullback-comparison,
quotient-pushout, noetherianity and finite-module completeness interfaces. It
introduces no independent literature assertion and no stronger assumption on
the original target group.
