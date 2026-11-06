# Scalar extension and reduced degree of central simple algebras

Let `K` be any field and `A` a unital, possibly noncommutative `K`-algebra. The field, algebra, and extension field have independent universes. For `[FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]`, this module proves that every field extension `L/K` preserves central simplicity. It constructs an actual matrix chart over the algebraic closure and the positive reduced degree. There is no restriction on characteristic, and simplicity or splitting after extension is not an input.

The public declarations are in `Langlands.CentralSimple`:

- `isSimpleRing_baseChange K A L` proves `IsSimpleRing (L ⊗[K] A)`.
- `isCentral_baseChange K A L` proves `Algebra.IsCentral L (L ⊗[K] A)`.
- `exists_matrix_chart K A L`, for algebraically closed `L`, gives a positive matrix size and an actual `L`-algebra equivalence from `L ⊗[K] A` to full matrices. Positivity is expressed by `NeZero`.
- `reducedDegree K A` is `Nat.sqrt (Module.finrank K A)`. `reducedDegree_pos`, the instance `reducedDegree_neZero`, and `finrank_eq_reducedDegree_mul_self` prove that this is positive and its square is the dimension. Positivity needs finite dimensionality and simplicity; the square identity also uses centrality.
- `finrank_eq_matrix_size` and `matrix_size_eq_reducedDegree` identify the size of any splitting chart, over any field extension. These two comparisons assume a supplied chart and do not require simplicity, centrality, or algebraic closedness.
- `reducedDegree_baseChange` proves invariance under field extension.
- `exists_matrix_chart_reducedDegree` gives a chart of the prescribed reduced degree over any algebraically closed extension. `algebraicClosureChart` chooses an actual such equivalence over `AlgebraicClosure K`.

The two preservation results are theorems, so consumers may install their conclusions locally when using typeclass-based results. The enveloping action `instModuleTensorProductMop` is likewise installed only locally in this module.

## Implemented proof

First, `isSimpleModule_enveloping` proves simplicity of the two-sided regular module for `A ⊗[K] Aᵐᵒᵖ`: a submodule is a two-sided ideal, using multiplication by the pure tensors `a ⊗ 1` and `1 ⊗ op b`. For `envelopingEnd_eq_smul`, an endomorphism of this module is both left and right multiplication by its value at one. That value is central, hence a scalar from `K`.

Every `K`-linear endomorphism consequently commutes with all enveloping-module endomorphisms. Mathlib's `jacobson_density`, applied to the finite image of a basis, gives an enveloping element acting as the specified linear endomorphism on every basis vector. Basis extensionality proves `mulLeftRight_surjective`: the map `AlgHom.mulLeftRight K A` onto `Module.End K A` is surjective. Only this surjectivity, rather than an enveloping algebra isomorphism, is asserted here.

The pure-tensor identity `baseChange_mulLeftRight_tmul` says that the scalar extension of `a * (·) * b` is multiplication on the left and right by `1 ⊗ a` and `1 ⊗ b`. Tensor induction and surjectivity then prove `baseChange_mem_ideal`: every extended `K`-linear operator preserves every two-sided ideal of `L ⊗[K] A`.

For simplicity, take a nonzero element of a nonzero ideal and a nonzero coordinate in the scalar-extended finite basis. Extend the `K`-linear map sending an element to that coordinate times one. Tensor induction identifies its value on the chosen ideal element with `c ⊗ 1`, where `c` is the nonzero `L`-coordinate. The ideal therefore contains `c ⊗ 1`; multiplying by `c⁻¹ ⊗ 1` puts one in the ideal. Nontriviality of the tensor algebra follows from flatness over the field and injectivity of the scalar map into `A`.

For centrality, `baseChange_mulLeftRight_central` shows that an extended enveloping operator on a central element acts by its value at one. Choose a `K`-linear functional taking one to one, and compose it with scalar multiplication on one in `A`. Its extension fixes each central element by the previous identity and surjectivity. Tensor induction shows that all its values have the form `c ⊗ 1`. Thus every central element is a scalar from `L`.

Mathlib's `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` now supplies the full matrix chart over an algebraically closed extension. The dimension calculation uses `Module.finrank_baseChange`, the chart's linear equivalence, and `Module.finrank_matrix`. In particular the dimension is a square. The natural square root is the matrix size by `Nat.sqrt_eq`; the algebraic closure provides a chart without any splitting hypothesis. Classical choice selects `algebraicClosureChart` from this proved existence.

## Sources and scope

The original source is J. S. Milne, *Algebraic Groups* (2022 corrected reprint), Chapter 24d, Theorem 24.19 and footnote 3, printed p. 521 / PDF p. 532. The theorem asserts preservation of central simplicity by field extension, and the footnote distinguishes the reduced degree from the full vector-space dimension. Proposition 24.22, printed p. 522 / PDF p. 533, gives the splitting-form and square-dimension conclusion using a separable closure. Proposition 24.26, printed p. 523 / PDF p. 534, gives the enveloping algebra isomorphism. The retained author errata for the 2022 reprint contains no correction to these passages.

The proof here is an internal derivation in a different dependency order: Jacobson density proves enveloping surjectivity before scalar-extension simplicity. Milne's proof of Proposition 24.26 instead uses simplicity after extension; using that proof here would be circular. The chart proved here uses the algebraic closure and Mathlib's algebraically closed classification. It does not assert splitting over a separable closure, a finite separable or Galois splitting extension, determinant descent, or the reduced-norm law. Those are separate obligations of the reduced-norm construction. In particular, an algebraic-closure chart alone does not justify coefficient descent to an imperfect base field by fixed points of automorphisms.
