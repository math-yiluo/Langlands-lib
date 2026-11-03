# Finite type algebras are countably generated modules

This module proves one lemma used in the proof of
`Langlands.CommutativeAlgebra.IntegralFibreProjectivityStatement` (Stacks Project, Tag 05FT).
The projectivity criterion `Langlands.CommutativeAlgebra.projective_of_locallySplit_baseChange`
needs the module to be countably generated, and this lemma supplies that hypothesis for a finite
type algebra.

## Statement

`Langlands.CommutativeAlgebra.exists_countable_span_eq_top`: let `R` and `S` be commutative rings
and `S` an `R`-algebra of finite type (`Algebra.FiniteType R S`). Then there is a countable set
`s ⊆ S` whose `R`-linear span is all of `S`.

## Proof

By `Algebra.FiniteType.iff_quotient_mvPolynomial''` there are `n : ℕ` and a surjective
`R`-algebra map `f : MvPolynomial (Fin n) R →ₐ[R] S`. The monomials form the basis
`MvPolynomial.basisMonomials (Fin n) R`, indexed by `Fin n →₀ ℕ`, which is countable. Take `s` to
be the image of this basis under `f`. It is countable as the image of a range over a countable
type. Its span is the image under `f` of the span of the basis (`Submodule.span_image`), which is
the range of `f`, and this is `⊤` because `f` is surjective.

## Provenance

This is a standard fact, stated here because the 05FT proof needs it. It is internal to the
project; Worker 281 proposed the statement and Worker 928 proved it.
