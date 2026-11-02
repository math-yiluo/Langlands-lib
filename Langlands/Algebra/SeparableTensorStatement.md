# Tensor decomposition of a finite separable field extension

`Langlands.Algebra.SeparableTensor.EmbeddingEvaluationStatement` states that
`embeddingEvaluation k K Ω` is bijective when:

- `k`, `K` and `Ω` are fields;
- `K` and `Ω` have `k`-algebra structures;
- `K/k` is finite dimensional and separable;
- for every `x : K`, the minimal polynomial `minpoly k x` splits after mapping its
  coefficients into `Ω`.

The conclusion concerns the specified canonical map of `Ω`-algebras
`Ω ⊗[k] K → ((K →ₐ[k] Ω) → Ω)`, with value `c * σ(x)` on the `σ` coordinate of
`c ⊗ x`. In particular, the conclusion provides a specific algebra isomorphism,
by equipping this map with the inverse supplied by its bijectivity.

The source is Milne, *Algebraic Groups* (2017), 2.61, printed p.59 / PDF p.75:
the tensor decomposition of a finite étale algebra over a field containing its
conjugates. This statement specializes the finite étale algebra to a finite
separable field extension. It gives the splitting-field hypothesis as the
explicit splitting of all minimal polynomials, so no choice of a common
algebraic closure or inclusion `K → Ω` is required. This is a derived equivalent
field formulation of that hypothesis. The order of the tensor factors is
reversed from the displayed source formula, using the commutative tensor
symmetry.

The resulting decomposition is the algebraic prerequisite for splitting the
published `WeilGm.groupScheme k K` after base change. This proposition does not
itself state a group-scheme isomorphism, a Galois action, or a torus lattice
classification.

Source: registered `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
