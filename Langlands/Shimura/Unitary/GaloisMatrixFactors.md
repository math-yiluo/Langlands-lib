# Galois transport between individual matrix factors

This module constructs the actual semilinear ring equivalence from the matrix
factor labelled by `i : K →+* ℂ` to the factor labelled by `s ∘ i`. It retains
exactly the Harris-chart, number-field, CM-section, algebra and finite-basis
inputs of `GaloisEmbeddingMatrices`. Its provenance is internal: it derives the
factor maps from that module's constructed full-product action and center
identity. No factor permutation or chart equivalence is assumed.

`ComplexMatrix.singleFactor i M` is the function equal to `M` at `i` and zero
elsewhere. Its evaluation lemmas hold for any index type and type with zero.
`sum_singleFactor` reconstructs a function by summing these functions when the
index set is finite and the values form an additive commutative monoid.

Write `T_s` for `C.embeddingMatrixGaloisEquiv hΦ b s`.
`embeddingMatrixGaloisEquiv_single_zero` proves

\[
  T_s(\operatorname{single}_i M)(j)=0 \quad\text{if }j\ne s\circ i.
\]

Distinct ring embeddings differ at some `k : K`. Multiplying the input by the
center function `l ↦ scalar(l(k))` has the same effect as multiplication by the
complex scalar `i(k)`. Applying `T_s`, its multiplicativity, center invariance
and semilinearity gives, in the `j`-th output factor,

\[
  j(k)\,T_s(\operatorname{single}_i M)(j)
   =s(i(k))\,T_s(\operatorname{single}_i M)(j).
\]

The chosen scalars differ, so their nonzero difference annihilates that matrix
only if the matrix is zero. The Lean proof uses `sub_smul` and `smul_eq_zero`
in the complex matrix module.

`embeddingMatrixGaloisEquiv_factor` then proves that `T_s(x)(s∘i)` depends only
on `x(i)`: it equals the value obtained from `singleFactor i (x i)`.
The set of embeddings is finite because `K` is a number field. Decompose `x`
as the finite sum of its supported factors, apply additivity of `T_s`, and
use the previous vanishing theorem for every summand except `i`. Injectivity
of postcomposition by `s` identifies the unique surviving index.

`embeddingFactorGaloisHom s i` sends `M` to
`T_s(singleFactor i M)(s∘i)`. Addition, multiplication and zero follow from
those properties of the supported functions and of `T_s`. The unit law uses
the factor-dependence identity applied to the full product's unit; it does
not incorrectly identify a single supported unit with the full unit.
The module exposes the full-product evaluation formula and proves

\[
  F_{s,i}(zM)=s(z)F_{s,i}(M),\qquad
  F_{s,i}(\operatorname{ev}_i(a))=\operatorname{ev}_{s\circ i}(a).
\]

The first identity follows from support compatibility with scalar
multiplication and semilinearity of `T_s`. The second combines the
factor-dependence formula with invariance of original-algebra evaluations.

The factor homomorphism is injective: equal output matrices give equal full
images of their supported inputs, since both images vanish at every other
factor. Injectivity of `T_s` and evaluation at `i` then give equal inputs.
It is surjective: take the inverse image under `T_s` of a matrix supported
at `s∘i`, and evaluate that preimage at `i`. The factor-dependence formula
shows this is a preimage of the desired matrix.
`embeddingFactorGaloisEquiv` packages these two proofs into a ring equivalence;
its forward function is the constructed factor homomorphism.

The result establishes the embedding permutation `i ↦ s∘i` for the actual
algebra transport. It retains chart and basis dependence. Expressing each
factor map as entrywise application of `s` followed by an inner matrix
automorphism, and the later scheme-cocharacter reflex comparison, are not
claimed here.
