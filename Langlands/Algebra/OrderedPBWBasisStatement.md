# Finite-basis PBW proposition over arbitrary fields

Author: Worker 1431.

`Langlands.Algebra.UniversalEnveloping.OrderedPBWBasisStatement.{u,v}` is a
Prop-valued definition of the finite-basis Poincare–Birkhoff–Witt assertion.
It quantifies over every field `k : Type u`, every Lie ring `L : Type v`
with `LieAlgebra k L`, every natural `n`, and every supplied basis
`b : Module.Basis (Fin n) k L`. The universes `u` and `v` vary independently.
Its conclusion is the conjunction

```lean
LinearIndependent k (orderedPBWMonomial b) ∧
  Submodule.span k (Set.range (orderedPBWMonomial b)) = ⊤
```

Both clauses refer to the actual `UniversalEnvelopingAlgebra k L`.
The family is indexed by all exponent vectors `e : Fin n → ℕ`.
The imported module `Langlands.Algebra.OrderedPBWMonomials` defines it as
the product of the powers of `UniversalEnvelopingAlgebra.ι k (b i)` in
ascending `Fin n` order. Independence forbids finite nontrivial linear
relations among these indexed monomials; the full-span equality asserts that
every element of the quotient algebra is a finite linear combination of them.
Together these give precisely the basis assertion.

There is no restriction on the characteristic. In characteristic two,
Mathlib's `LieRing` still requires `[x,x] = 0`, as does the cited source.
There is no positivity assumption on `n`. For `n = 0` there is a single
exponent vector, and the construction's `orderedPBWMonomial_empty` identifies
its monomial with one; the proposition retains both basis clauses in that case.
The supplied basis already expresses finite dimension, so no additional
finite-dimensionality assumption is needed.

The source is Anne V. Shepler and Sarah Witherspoon,
*Poincare-Birkhoff-Witt Theorems*, retained 2014 author PDF, Section 2,
printed/PDF pages 2–3, especially the displayed **PBW Basis Theorem** on page 3.
The preceding field and alternating-bracket conventions are on page 2.
The tensor-quotient construction on page 3 agrees with Mathlib's
`UniversalEnvelopingAlgebra`; the source's ordered indices `1,...,n` are
represented by `Fin n`. The indexed independence and full-span clauses are
the explicit Lean expansion of the source's ordered monomials forming a basis.
The empty-basis case follows the same product convention.

This file defines the proposition without proving or assuming it. There is
no PBW premise, generator-injectivity premise, normal-form certificate,
polynomial-algebra equivalence, characteristic-zero assumption, semisimplicity
assumption, or algebraic-group realization. A separate proof can target this
exact proposition after its publication.

Registered source: `shepler-witherspoon-2014-pbw-theorems`, retained at
`literature/Poincare-Birkhoff-Witt Theorems.pdf`, SHA256
`4a7ac216c3ff4214ff953d2f8bd1643db8213822b68a5585155de2c5a1682d4a`.
