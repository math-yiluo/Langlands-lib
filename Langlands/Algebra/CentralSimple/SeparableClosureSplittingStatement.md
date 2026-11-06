# Central simple algebras split over a separable closure

`Langlands.CentralSimple.SeparableClosureSplittingStatement.{u}` states that,
for every field `K : Type u` and unital ring `A : Type u` with a `K`-algebra
structure, finite dimension, centrality and ring simplicity, there are a positive
integer `d` and an actual algebra equivalence

```text
SeparableClosure K ⊗[K] A ≃ₐ[SeparableClosure K]
  Matrix (Fin d) (Fin d) (SeparableClosure K).
```

The existential uses `Nonempty` to package the equivalence as a proposition.
It assumes neither a splitting chart nor simplicity or centrality after scalar
extension. There is no restriction on the characteristic or on `u`.
This file defines a proposition; it does not prove it.

The source is J. S. Milne, *Algebraic Groups*, corrected reprint (2022),
Chapter 24d, Theorem 24.19 and Propositions 24.21–24.22, printed pages 521–522
(PDF pages 532–533). The registered source is
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`,
at `literature/J. S. Milne - Algebraic Groups- The Theory of Group Schemes of Finite Type over a Field (2022 corrected reprint).pdf`.
The complete retained author errata snapshot for the 2022 reprint, retrieved
4 November 2026, was read and contains no correction to these passages.

Milne writes the tensor factors in the opposite order; the displayed statement
uses the standard extension-of-scalars order. Milne's footnote 3 calls
`dim_K A` the degree and `d` the reduced degree. Here `d` is the matrix size.
The finite Galois descent and the dimension identity are separate obligations;
this proposition alone supplies neither a finite extension nor those proofs.
