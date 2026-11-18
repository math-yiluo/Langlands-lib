# Coefficient automorphisms over a quotient base

Let `R` be a commutative ring, `I` any ideal, and `M` a module over `R/I`
with a compatible `R`-module structure. For any commutative `R`-algebra `B`,
the canonical `B`-linear coefficient equivalence identifies

`((R/I) ⊗[R] B) ⊗[R/I] M` with `B ⊗[R] M`.

`coefficientEquiv` reuses the published generic
`ElementaryKernelTensor.coefficientTensorEquiv`. The actual base-changed
algebra is equipped with the `B`-action through its right tensor factor.
The map from `B` to `(R/I) ⊗[R] B` is surjective, since `R → R/I` is
surjective.

`linearEquivOfSurjectiveAlgebra` is the elementary scalar lemma: an
`A`-linear equivalence between compatible `S`-modules is `S`-linear whenever
`A → S` is surjective. The proof represents a scalar of `S` by one of `A`
and applies the original linearity. This helper works over a commutative
semiring `A` and a semiring `S` with additive commutative module monoids.

`descendAutomorphism` conjugates a `B`-linear automorphism of `B ⊗[R] M`
through coefficient rearrangement, then uses that scalar lemma to make the
result linear over `(R/I) ⊗[R] B`. Its characterization after rearrangement is
`coefficientEquiv (descendAutomorphism(e)(z)) = e(coefficientEquiv(z))`.
`descendAutomorphismHom` proves that this operation preserves the identity and
composition of automorphisms.

`coefficientEquiv_naturality` proves compatibility with every morphism of
coefficient algebras by tensor induction. The final naturality lemma then
shows that any compatible pair of original automorphisms gives a compatible
pair of quotient-base automorphisms, by applying the injective coefficient
equivalence and the characterization above.

This is internal derived scalar and tensor algebra. It requires neither
flatness nor a square-zero condition on `I`. It supplies no original group
action or geometric kernel comparison; those remain separate inputs for the
deformation application.
