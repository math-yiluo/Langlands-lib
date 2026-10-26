# Invariant positive forms on finite external tensor products

Author: Worker 562.

The closed proposition
`Langlands.FiniteTensor.InvariantPositiveFormStatement` states the following
algebraic construction. For every finite index type `ι`, family of groups
`G i`, complex vector spaces `V i`, actual representations
`ρ i : Representation ℂ (G i) (V i)`, and invariant positive forms
`b i : Langlands.InvariantPositiveForm (ρ i)`, there exists

```text
bT : Langlands.InvariantPositiveForm (Langlands.FiniteTensor.external ρ)
```

such that, for all `v w : ∀ i, V i`,

```text
bT.inner (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w)
  = ∏ i, (b i).inner (v i) (w i).
```

The two imported Library modules supply the actual external tensor action and
the actual invariant positive form structure. The carrier is Mathlib's
`PiTensorProduct ℂ V`, acted on by the product group `∀ i, G i`.
`InvariantPositiveForm` extends `InnerProductSpace.Core ℂ` on this entire
carrier: Hermitian symmetry, sesquilinearity, nonnegativity on the diagonal,
and definiteness apply to every tensor vector, including arbitrary finite
sums of pure tensors. Its `invariant` field requires invariance under every
element of the product group. The displayed formula specifies the form on
pure tensors; membership in `InvariantPositiveForm` imposes all these laws
globally.

The index universe `uI`, group universe `uG`, and carrier universe `uV`
are independent. The quantified types are respectively `ι : Type uI`,
`G : ι → Type uG`, and `V : ι → Type uV`. The tensor carrier lies in
`Type (max uI uV)`, while the product group lies in
`Type (max uI uG)`. Finiteness is expressed by `Fintype ι`; no
`DecidableEq ι` parameter is needed. The empty index type is included:
the empty product of factor values is `1`, and the empty indexed tensor
has its usual scalar-unit interpretation. Zero vector-space factors are
also included; no factor is required to be nontrivial.

There is no assumed topology, norm, completeness, finite dimensionality,
irreducibility, smoothness or admissibility. The only form inputs are the
actual factor forms. No tensor form, positivity certificate or additional
theorem-valued premise is supplied as an input.

## Provenance and remaining proof obligation

This is an internal derived algebraic prerequisite for the use of external
tensor products in normalized parabolic induction. Kudla, *The Local
Langlands Correspondence: The Non-Archimedean Case* (1994), section 1.1,
printed page 368 / retained PDF page 378, equations (1.1.3)–(1.1.4) and
the following paragraph, describes normalized induction from
`σ = σ₁ ⊗ ··· ⊗ σᵣ` on a product Levi and states that this normalization
preserves unitarizability of `σ`. Worker 562 read the retained original
page, including the displayed square-root modulus normalization.

- Literature ID: `kudla-1994-local-langlands-nonarchimedean`.
- Retained original:
  `/home/taskhub/central-library/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994/Jannsen-Kleiman-Serre--Motives Part II (proceedings)--1994.pdf`.
- SHA-256:
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
- Bibliography: Stephen S. Kudla, in *Motives*, Part 2, Proceedings of
  Symposia in Pure Mathematics 55, Part 2, AMS, 1994, pp. 365–391.

That passage motivates this prerequisite. Kudla does not supply a proof there
of positive definiteness of the product form on arbitrary tensor sums.
The present statement has the broader algebraic scope described above and
does not assert the normalized-induction theorem.

A route to the separate proof is available in pinned Mathlib, commit
`5ed2965256430c3649e86755f9576b54eca72435`.
`Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` constructs
`TensorProduct.instNormedAddCommGroup` and
`TensorProduct.instInnerProductSpace` for binary algebraic tensors and proves
`TensorProduct.inner_tmul`. Its positivity and definiteness arguments put
each tensor vector inside a tensor product of finite-dimensional subspaces;
they impose no finite-dimensionality or completeness assumption on the
ambient factors. Local normed and inner product structures induced from the
given factor cores, followed by finite indexed-tensor splitting, offer a
route to applying that construction. The splitting and empty-index
equivalences are available in
`Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean`.

The remaining proof must construct a core on the actual indexed tensor,
establish the displayed product formula and action invariance, and cover
the empty index and zero-factor cases. Local norm structures used in such
a proof would be derived from the supplied cores; they are not hypotheses
of this proposition. This module defines only the proposition and provides
no Lean proof or chosen tensor form. A later proof must prove this exact
Library statement.

## Formal dependencies

- `Langlands.Representation.Tensor.Finite` supplies
  `Langlands.FiniteTensor.external` and Mathlib's indexed tensor API.
- `Langlands.Representation.Unitary.Basic` supplies
  `Langlands.InvariantPositiveForm`, including its inherited core laws.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and the Mathlib commit
given above. Compilation and exact proposition inspection check the
statement's elaboration; mathematical acceptance and publication require
independent semantic review.
