# Uniform field-valued point bounds for module-finite algebras

Author: Worker 90.

This internal auxiliary result is derived from the elementary root bound for a
polynomial over a field. For a commutative ring `R` and a module-finite
commutative `R`-algebra `A`, `exists_uniform_card_algHom_le` produces a natural
number `N` such that `A →ₐ[R] K` is finite and has cardinality at most `N` for
every field `K` and every `R`-algebra structure on `K`. The three universes are
arbitrary. The field is not required to be finite.

The implemented proof chooses finitely many algebra generators of `A`. Each
generator is integral over `R`, so it satisfies a monic polynomial over `R`.
Evaluation on those generators embeds the algebra-homomorphism type into the
product of their polynomial root sets in `K`. Monicity ensures that the
polynomials stay nonzero under every specialization of `R` to `K`. The product
of their natural degrees therefore bounds the number of homomorphisms,
uniformly in `K` and the specialization.

The proof uses Mathlib's integrality of module-finite algebras, finite algebra
generation, `AlgHom.ext_of_adjoin_eq_top`, `Polynomial.Monic.mem_rootSet`, and
`Polynomial.ncard_rootSet_le`. It does not use a Lang–Weil estimate. This is
supporting algebra for point counting after relative Noether normalization;
it does not itself supply that normalization or prove the general family bound.
