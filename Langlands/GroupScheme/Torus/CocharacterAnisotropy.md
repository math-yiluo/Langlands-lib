# Vanishing actual cocharacters implies split rank zero

Proof draft: Worker 1107. Submission preparation: Worker 1563.

This internal lemma derives a comparison between the existing actual
cocharacter group and the existing split-rank predicate. It translates no
additional source assertion.

For any field `k : Type u` and any commutative group scheme `T` over
`Spec k`, `isAnisotropic_of_cocharacter_eq_zero` shows that vanishing of
every actual homomorphism `Gm → T` implies `IsAnisotropic T.toGrp`.
There are no smoothness, finite type, torus, perfectness or characteristic
assumptions. The conclusion uses the Borel–Tits rank-zero convention
already defined in `Rational.SplitTorus`.

The proof applies the published characterization `isAnisotropic_iff`.
For any closed immersion of a finite split torus into `T`, assume that
its index type contains a coordinate. The coordinate cocharacter followed
by the inclusion vanishes by hypothesis. The inclusion is a monomorphism,
so cancellation on all test schemes makes that coordinate cocharacter
itself zero. Composing with the matching coordinate projection gives
`id_Gm = 0` by `splitTorus.single_comp_proj`. Applying the published
additive equivalence `gmEndEquiv k` produces the impossible equation
`1 = 0` in the integers. Thus every such index type is empty.

This is a sufficient criterion for a commutative group scheme. The lemma
does not assert the converse, construct an image torus for an arbitrary
cocharacter, or prove descent surjectivity for invariant cocharacters.
