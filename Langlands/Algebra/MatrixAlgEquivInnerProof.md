# Proof: automorphisms of full matrix algebras are inner

This module proves `Langlands.MatrixAlgebra.AlgEquivIsInnerStatement.{uk, uI}`
from `Langlands.Algebra.MatrixAlgEquivInnerStatement`. It also proves the
chart-comparison corollary. It introduces no definitions.

## Declarations

- `Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv` takes a field `k`, a
  finite type `I` with decidable equality and
  `e : Matrix I I k ≃ₐ[k] Matrix I I k`. It gives a unit
  `U : (Matrix I I k)ˣ` with `e M = ↑U * M * ↑U⁻¹` for all `M`. This is the
  statement for fixed `k`, `I` and `e`, with implicit `k` and `I`, so it can
  be applied directly.
- `Langlands.MatrixAlgebra.algEquivIsInner :
  AlgEquivIsInnerStatement.{uk, uI}` is the target theorem. It introduces the
  binders and applies `exists_unit_conj_of_algEquiv`.
- `Langlands.MatrixAlgebra.exists_unit_conj_of_charts` is the chart
  corollary. Let `B : Type uB` be a `k`-algebra (`[Semiring B] [Algebra k B]`)
  and `φ ψ : B ≃ₐ[k] Matrix I I k` two charts. Then there is a unit
  `U : (Matrix I I k)ˣ` with `ψ b = ↑U * φ b * ↑U⁻¹` for every `b : B`. The
  universe `uB` is independent of `uk` and `uI`.

Like the statement, all three hold for every finite index type, the empty one
included. Neither the proof nor the corollary needs a nonemptiness hypothesis.
The empty case is covered by Mathlib's theorem below, which handles a
subsingleton `V` separately.

## Proof

The proof transports Mathlib's endomorphism-algebra theorem to matrices.
Mathlib's `AlgEquiv.eq_linearEquivConjAlgEquiv`, from
`Mathlib/LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean`, says that every
`f : Module.End K V ≃ₐ[K] Module.End K W` with `V`, `W` projective over a
semifield `K` has the form `T.conjAlgEquiv K` for some linear equivalence
`T : V ≃ₗ[K] W`. Here `T.conjAlgEquiv K f = T ∘ₗ f ∘ₗ T.symm`.

1. Put `ψ := LinearMap.toMatrixAlgEquiv' :
   Module.End k (I → k) ≃ₐ[k] Matrix I I k`, the standard `k`-algebra
   equivalence between endomorphisms of `I → k` and matrices.
2. Conjugate `e` back to endomorphisms with `(ψ.trans e).trans ψ.symm`, which
   sends `g` to `ψ.symm (e (ψ g))`. `I → k` is free and hence projective over
   the field `k`. Mathlib's theorem then gives `T : (I → k) ≃ₗ[k] (I → k)`
   with `(ψ.trans e).trans ψ.symm = T.conjAlgEquiv k`.
3. Define the unit `U` with value `ψ T` and inverse `ψ T.symm`. The two unit
   equations follow from multiplicativity of `ψ`, `ψ 1 = 1`, and
   `T ∘ T.symm = id = T.symm ∘ T`, checked pointwise with `ext` and `simp`.
4. For a matrix `M`, evaluate the equation from step 2 at `ψ.symm M` and apply
   `ψ`. Using `ψ (ψ.symm M) = M`, this gives
   `e M = ψ (T ∘ₗ ψ.symm M ∘ₗ T.symm)`. Composition in `Module.End` is
   multiplication (`Module.End.mul_eq_comp`), and `ψ` is multiplicative. So
   the right-hand side is `ψ T * M * ψ T.symm`, which is `↑U * M * ↑U⁻¹` by
   associativity and the definition of `U`.

For the corollary, apply `exists_unit_conj_of_algEquiv` to the automorphism
`φ.symm.trans ψ` of `Matrix I I k`. It sends `φ b` to `ψ (φ.symm (φ b)) = ψ b`.
Evaluating the resulting identity at `M = φ b` and simplifying gives the
claim.

The proof does not follow the source's route. Milne, *Class Field Theory*
v4.03, Chapter IV, Theorem 2.10 compares two module structures on `kⁿ`. The
Mathlib proof instead builds the linear equivalence directly from a rank-one
endomorphism and a dual vector. No literature is used beyond the statement's
citation.

## Checks

The development `lean_check` reports 0 errors and 0 warnings. The target
`algEquivIsInner` has kind theorem and level parameters `uk` and `uI`, and it
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. The
statement pair is unchanged.

## Attribution

Worker 277 authored the complete Lean proof and its explanation in the shared
draft. Worker 308 checked the draft against the published target and the pinned
Mathlib sources, and prepared the proof contribution for validation and independent
review.
