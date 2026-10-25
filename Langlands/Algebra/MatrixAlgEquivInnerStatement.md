# Automorphisms of full matrix algebras are inner

`Langlands.MatrixAlgebra.AlgEquivIsInnerStatement.{uk, uI}` is a Prop-valued
definition. It states the theorem and does not prove it.

## Statement

Let `k : Type uk` be a field and `I : Type uI` a finite type with decidable
equality (`[Fintype I] [DecidableEq I]`). `Matrix I I k` is the full matrix
algebra over `k`, with Mathlib's matrix multiplication, identity matrix and
scalar `k`-algebra structure. Every `k`-algebra automorphism

```text
e : Matrix I I k ≃ₐ[k] Matrix I I k
```

is inner. That is, there is a unit `U : (Matrix I I k)ˣ` of the matrix
algebra such that

```text
e M = (U : Matrix I I k) * M * ((U⁻¹ : (Matrix I I k)ˣ) : Matrix I I k)
```

for every `M : Matrix I I k`. Here `U⁻¹` is the inverse in the unit group,
coerced back to a matrix. The universe parameters `uk` and `uI` are
independent.

`e` is any algebra automorphism over `k`, so it is `k`-linear. Semilinear
automorphisms, which twist scalars by a field automorphism, are not covered.
The proposition takes no conjugating unit, module equivalence or
Skolem–Noether result as input; it only asserts that such a unit exists. It
says nothing about uniqueness of `U`.

## Index types, including the empty one

The index type is any finite type, not just `Fin n`. For `I = Fin n` with
`0 < n` this is the classical statement for `Mₙ(k)`. Any other nonempty
finite `I` is in bijection with some such `Fin n`.

The empty index type is included and needs no extra hypothesis. When `I` is
empty, `Matrix I I k` has exactly one element, so `1 = 0`. Every automorphism
is then the identity, and `U = 1` satisfies the formula trivially. This ring
is not simple, so the source's hypothesis fails in this case. The case lies
outside the source and is included only because the conclusion holds
trivially.

## Source and provenance

The source is J. S. Milne, *Class Field Theory*, v4.03 (2020), literature ID
`milne-2020-class-field-theory` (SHA256
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`).
Chapter IV, §2, *The Noether–Skolem Theorem* is on printed page 129 (PDF
page 138). Theorem 2.10 states: for homomorphisms `f, g : A → B` of
`k`-algebras with `A` simple and `B` central simple, there is an invertible
`b ∈ B` with `f(a) = b·g(a)·b⁻¹` for all `a`. Corollary 2.12 reads: "All
automorphisms of a central simple `k`-algebra are inner. For example, the
automorphism group of `Mₙ(k)` is `PGLₙ(k) = GLₙ(k)/k^×Iₙ`."

This module states the matrix-algebra case of Corollary 2.12, the example
given there: every `k`-algebra automorphism of `Mₙ(k)`, `n ≥ 1`, is
conjugation by an invertible matrix. In Lean, invertible matrices are units
of `Matrix I I k`, and indices come from a finite type `I`. The formula
`e M = U M U⁻¹` is the source's `f(a) = b·g(a)·b⁻¹` with `f = e`, `g` the
identity and `b = U`. The provenance is derived: this specialises Corollary
2.12 to matrix algebras, which are central simple over `k` when `I` is
nonempty. It adds the trivial empty case and leaves out the description of
the automorphism group as a quotient. Arbitrary central simple algebras and
the general Theorem 2.10 are not stated.

## Relation to Mathlib and the Library

The pinned Mathlib proves an endomorphism-algebra version.
`AlgEquiv.eq_linearEquivConjAlgEquiv`, in
`Mathlib/LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean`, says that every
`f : Module.End K V ≃ₐ[K] Module.End K W` with `V` and `W` projective over a
semifield `K` is `T.conjAlgEquiv K` for some linear equivalence `T`. Neither
Mathlib nor the Library had a statement in terms of matrices and units of
`Matrix I I k`. This module adds no new definition: conjugation is written
out in the formula.

This statement was requested as the matrix-algebra input for comparing
matrix charts in the Harris signature work. It imports no Harris or Shimura
modules. A comparison of two charts `B ≃ₐ[k] Matrix I I k` follows directly
by applying the statement to `φ.symm.trans ψ`; that corollary is not part of
this proposition.
