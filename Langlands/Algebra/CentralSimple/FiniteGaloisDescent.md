# Finite Galois descent of matrix splitting charts

This module constructs finite Galois descent of an actual matrix splitting
chart. All declarations are in `Langlands.CentralSimple`. The fields `K`, `E`
and the unital ring `A` belong to an arbitrary common universe `u`, with
`K`-algebra structures on `E` and `A`.

Given `[FiniteDimensional K A]`, `[IsGalois K E]` and an actual chart

```text
e : E ⊗[K] A ≃ₐ[E] Matrix (Fin d) (Fin d) E,
```

`finiteGaloisMatrixChartField e` is a `FiniteGaloisIntermediateField K E`.
Its underlying intermediate field `L` therefore carries proved finite
dimension and Galois instances over `K`. The construction
`finiteGaloisMatrixChart e` is an actual equivalence

```text
L ⊗[K] A ≃ₐ[L] Matrix (Fin d) (Fin d) L.
```

The theorem `exists_finiteGalois_matrix_chart` packages these same constructions
as an existential proposition. Separately, `finrank_eq_matrixSize e` proves
`Module.finrank K A = d * d` for any field-extension chart, without a Galois
hypothesis. The module imposes no characteristic restriction. It makes no
positivity claim about `d`; the same size is preserved by descent.

The implemented proof has three steps.

1. `matrixChartRepresentation e` sends `a : A` to `e (1 ⊗ a)`.
   `matrixChartCoefficients e` is the range of its entries on
   `Module.finBasis K A`, indexed by the finite product
   `Fin (Module.finrank K A) × Fin d × Fin d`.
   `finiteGaloisMatrixChartField e` uses Mathlib's
   `FiniteGaloisIntermediateField.adjoin` to adjoin these entries and take
   their normal closure inside `E`. This is finite Galois because `E/K` is
   Galois. Expanding every `a` in the finite basis proves
   `matrixChartRepresentation_mem_finiteGaloisField`: all entries of its
   representation lie in `L`.
2. `restrictMatrixEntries` restricts any algebra representation whose entries
   lie in an intermediate field. `restrictedMatrixChartHom` extends it from
   `A` to `L ⊗[K] A` by `AlgHom.liftEquiv`. The compatibility theorem
   `restrictedMatrixChartHom_coe` identifies this map, after including matrix
   entries into `E`, with the original chart after the tensor inclusion.
   Its proof checks pure tensors and addition.
3. The tensor inclusion is injective by
   `TensorProduct.map_injective_of_flat_flat`, since modules over a field
   are flat. The original chart is injective, so compatibility proves
   `restrictedMatrixChartHom_injective`. The chart over `E` fixes
   `finrank K A = d * d`. Scalar-extension dimension and the matrix dimension
   formula give equal finite dimensions over `L`; injectivity then gives
   surjectivity. `restrictedMatrixChart` packages the bijective algebra
   homomorphism as an algebra equivalence.

This is a derived linear algebra construction using the pinned Mathlib tensor,
dimension and Galois-closure theorems. Its role is the finite-coordinate
descent step in Milne, *Algebraic Groups*, corrected reprint (2022),
Chapter 24d, proof of Theorem 24.23, printed page 522 (PDF page 533),
registered as `milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The complete retained 2022 author errata snapshot was read and contains no
correction to that passage. The explicit basis-coordinate construction and
flatness proof above are the implemented derivation, rather than a transcription
of Milne's proof.

This helper consumes a chart over a Galois extension. It does not prove that a
central simple algebra admits such a chart, and it does not assume simplicity
of any scalar extension. The unconditional central simple splitting theorem
requires a separate construction of the chart over a separable closure.
