# Augmented inverse-adjoint matrix representation

## Construction and scope

For `I : Type u` with `Fintype I` and `DecidableEq I`, the index
`InverseAdjointIndex I` is `Unit ⊕ (I ⊕ I)`. The definition
`inverseAdjointMatrix A` is the block diagonal matrix

\[
  \rho(A)=\operatorname{diag}(1,A,(A^{-1})^H),\qquad A\in\mathrm{GL}(I,\mathbb C).
\]

Here the inverse is the group inverse of `Matrix.GeneralLinearGroup I ℂ` and
`H` is conjugate transpose. The scalar, standard, and inverse-adjoint entry
formulas are `inverseAdjointMatrix_scalar`, `inverseAdjointMatrix_standard`,
and `inverseAdjointMatrix_dual`. Off-diagonal blocks are zero by the displayed
`Matrix.fromBlocks` definition.

`inverseAdjointMatrixHom` is the resulting matrix-valued monoid homomorphism.
`inverseAdjointRepresentation` composes it with Mathlib's star algebra
equivalence `Matrix.toEuclideanCLM`. Its codomain consists of actual complex
continuous linear endomorphisms of the Hilbert space
`EuclideanSpace ℂ (InverseAdjointIndex I)`. The theorem
`inverseAdjointRepresentation_apply` identifies this action with matrix-vector
multiplication in coordinates. The endomorphism multiplication is composition.
Because the source is a group, the homomorphism law also makes every output
invertible.

The universe `u` is arbitrary. There is no nonemptiness hypothesis on `I`.
The construction and all proofs include empty `I`, when only the scalar block
remains. No growth-comparison theorem or archimedean specialization is part of
this unit. Only published Mathlib modules are imported.

## Intrinsic properties and proofs

`inverseAdjointMatrix_one` and `inverseAdjointMatrix_mul` follow from block
multiplication. Inversion and conjugate transpose each reverse products,
so their composite preserves product order.

`isClosedEmbedding_inverseAdjointMatrix` establishes a closed embedding into
the **entire matrix space**. First, `Units.isClosedEmbedding_embedProduct`
embeds a unit as its value and inverse; a product homeomorphism removes the
multiplicative opposite from the second coordinate. Next, the injective
finite-dimensional real-linear map

\[
 (A,B)\longmapsto\operatorname{diag}(0,A,B^H)
\]

is a closed embedding by Mathlib's finite-dimensional linear-map theorem.
Translation by `diag(1,0,0)` adds the scalar block. Injectivity of the block map
is proved by reading the standard block and conjugating the entries of the
last block. This block map is real-linear, not complex-linear as a function
of the input matrices. Each output matrix still acts complex-linearly on
the Hilbert space.

`isClosedEmbedding_inverseAdjointRepresentation` transfers this result
through the finite-dimensional continuous linear equivalence underlying
`Matrix.toEuclideanCLM`. Thus closedness also holds in the full space of
complex continuous linear endomorphisms. Both versions export separate
continuity, injectivity, and closed-range corollaries.

For unitary input, uniqueness of inverse gives `A⁻¹ = Aᴴ`, hence the represented
matrix is `diag(1,A,A)`, as proved by `inverseAdjointMatrix_of_unitary`.
Block multiplication proves `inverseAdjointMatrix_mem_unitary`. The star
algebra equivalence transports this result to
`inverseAdjointRepresentation_mem_unitary`, and
`inverseAdjointRepresentation_inner` states preservation of the actual
complex Hilbert inner product.

## Hilbert–Schmidt normalization

`inverseAdjointHilbertSchmidtSq` is the sum of squared absolute values of all
entries of `ρ(A)`. The theorem `inverseAdjointHilbertSchmidtSq_eq` expands the
blocks and interchanges the finite summation indices in the last block to give

\[
  \operatorname{HS}^2(A)
  =1+\sum_{i,j}\lVert A_{ij}\rVert^2
    +\sum_{i,j}\lVert(A^{-1})_{ij}\rVert^2.
\]

The equality with the real part of the matrix trace of `ρ(A)ᴴ * ρ(A)` is
`inverseAdjointHilbertSchmidtSq_eq_matrix_trace`. Its proof expands the
diagonal of the product, uses `conj(z) * z = ‖z‖²`, and swaps the finite sums.
The theorem `inverseAdjointHilbertSchmidtSq_eq_trace` identifies the same
quantity with the real part of `LinearMap.trace` of
`star (inverseAdjointRepresentation A) * inverseAdjointRepresentation A`.
Here `star` is Mathlib's actual Hilbert-space adjoint. This identification
uses preservation of multiplication and adjoints by `Matrix.toEuclideanCLM`,
then computes the linear trace in the standard orthonormal basis.

`inverseAdjointHilbertSchmidtNorm` is the nonnegative real square root of this
quantity. The theorem with suffix `_eq_trace` gives the source's actual trace
normalization; `_sq` gives the displayed block formula for its square.
The square and the norm are both at least one and strictly positive, by
nonnegativity of the entry squares and monotonicity of square root. In
particular the bound holds for empty `I`. The norm is continuous because
its square is a finite sum of continuous squared entry norms and square root
is continuous.

## Original source and derived content

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
in *Automorphic Forms, Representations and L-Functions*, Proceedings of
Symposia in Pure Mathematics 33, Part 1 (1979), pp. 189–202, §1.2, printed
pp. 189–190, one-based PDF pages 184–185.

Registered source: `borel-jacquet-1979-automorphic`. Retained source:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
Both cited pages were read directly. No project errata note for this source
was available in the Library or shared notes at authoring time.

Section 1.2 defines the representation norm through the trace of the
adjoint times the operator, requiring finite kernel and image closed in the
endomorphism space. Its remark on p. 190 proposes adjoining the inverse-adjoint
representation and gives the associated square norm. The present generic
complex-GL construction specializes that remark; its injectivity is stronger
than finite kernel. The additional one-dimensional trivial summand is an
explicit derived normalization, not a claim that the original remark
includes it. It supplies the extra `1` and the lower bound even for empty
`I`. The concrete index, real-linear closed-embedding proof, Euclidean action,
and implementation lemmas are internal formalization choices derived from
this construction. All intrinsic properties are proved; none are assumed
as representation structure fields.
