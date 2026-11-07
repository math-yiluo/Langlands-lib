# Matrix splitting of a central simple algebra over a separable closure

Lean module: `Langlands.Algebra.CentralSimple.SeparableClosureChart`
(`Langlands/Algebra/CentralSimple/SeparableClosureChart.lean`).

## Mathematical content

Let `K` be a field and `A` a finite-dimensional central simple algebra over `K`
(in Lean: `[Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
[Algebra.IsCentral K A] [IsSimpleRing A]`), and let `d = reducedDegree K A`, the
natural square root of `Module.finrank K A`. For every separably closed field
`E` containing `K`, the scalar extension `E ⊗[K] A` is isomorphic as an
`E`-algebra to `Matrix (Fin d) (Fin d) E`; in particular this holds for Mathlib's
separable closure `SeparableClosure K` (the separable closure of `K` inside
`AlgebraicClosure K`).

This is Milne, *Algebraic Groups* (2022 corrected reprint), Proposition 24.22,
printed p. 522 (PDF p. 533), the direction used in its proof: "Let `A` be a central
simple algebra over `k`. Then `A ⊗ k_s` is again central simple (24.19), and so it
is isomorphic to `M_n(k_s)` with `n² = [A : k]` (see 24.21)." Milne's `n` is the
reduced degree of footnote 3 (printed p. 521, PDF p. 532), which is
`reducedDegree K A` here.

The module assumes no splitting extension, chart, or scalar-extension simplicity:
those are proved in the imported Library modules.

## Declarations

- `sepClosedExtensionChart K A E : (E ⊗[K] A) ≃ₐ[E]
  Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) E`, for any field
  `E` with `[Algebra K E] [IsSepClosed E]` (in any universe). A chosen chart; no
  claim is made about which one.
- `separableClosureChart K A : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
  Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) (SeparableClosure K)`,
  the case `E = SeparableClosure K`.
- `exists_separableClosure_matrix_chart K A`: there is `d` with `0 < d`,
  `Module.finrank K A = d * d`, and an `SeparableClosure K`-algebra equivalence
  `SeparableClosure K ⊗[K] A ≃ₐ Matrix (Fin d) (Fin d) (SeparableClosure K)`
  (witness `d = reducedDegree K A`).

## Implemented proof

1. Scalar extension (Milne 24.19) is supplied by
   `Langlands.Algebra.CentralSimpleScalarExtension`: `isSimpleRing_baseChange K A E`
   and `isCentral_baseChange K A E` show that `E ⊗[K] A` is a central simple
   `E`-algebra; Mathlib provides `FiniteDimensional E (E ⊗[K] A)`.
2. The separably closed classification (Milne 24.21) is
   `Langlands.Algebra.CentralSimple.SeparablyClosedSplitting`: `sepClosedChart E
   (E ⊗[K] A)` is a chart of size `Nat.sqrt (finrank E (E ⊗[K] A))`.
3. `reducedDegree_baseChange K A E` identifies that size with
   `reducedDegree K A` (because `finrank E (E ⊗[K] A) = finrank K A`); the chart is
   transported along `Matrix.reindexAlgEquiv E E (finCongr _)`.
4. The existence statement takes this chart together with `reducedDegree_pos K A`
   and `finrank_eq_reducedDegree_mul_self K A`.
