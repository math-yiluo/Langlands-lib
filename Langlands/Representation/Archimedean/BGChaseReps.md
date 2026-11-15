# Representations and integral weights (helpers for the Bernstein–Gelfand chase)

Module: `Langlands.Representation.Archimedean.BGChaseReps`, namespace
`Langlands.Archimedean.BGChase`. This module holds standard finite-dimensional
representation-theoretic constructions used by the formalization of Bernstein–Gelfand 1980, 5.10
(see `ComplexJacquetBimoduleReduction.md`). Everything here is proved. Nothing is taken from the
literature beyond textbook linear algebra. All representations are complex, and `End` carries the
commutator bracket (`LieRing.ofAssociativeRing`).

## Constructions of representations (any complex Lie algebra `L`)

- `tensorLie σ τ`: the tensor product representation `Y ↦ σ(Y) ⊗ 1 + 1 ⊗ τ(Y)` on `W ⊗ N`.
  `tensorLie_tmul` evaluates it on pure tensors.
- `homLie σ τ`: the representation `ψ ↦ τ(Y) ∘ ψ - ψ ∘ σ(Y)` on `Hom(W, N)`. `homLie_apply`
  evaluates it.
- `restrictLie σ S hS`: the restriction of `σ` to an invariant subspace `S`. `restrictLie_apply`
  says the inclusion intertwines.

In each case the Lie bracket condition is checked by direct computation.

## Weights

For a family `H : Fin n → End W` of operators:

- `IsWt H m w` means `H p w = m_p w` for all `p`, with `m : Fin n → ℤ`;
- `wtSpace H m` is the corresponding weight space;
- `intSpan H` is the span of all vectors of integral weight; `intSpan_eq_iSup` writes it as the
  supremum of the weight spaces;
- `mem_of_sum_mem` (elimination of weight components): if a finite sum of weight vectors with
  pairwise distinct weights lies in an `H`-invariant subspace `S`, then so does each summand.
  The proof is by strong induction on the set of weights: apply `H p - m'_p`, where `p`
  separates two of the weights.
- `mem_span_wt_of_mem`: consequently, an `H`-invariant subspace `S` meets `intSpan H` in the span
  of the weight vectors lying in `S`;
- `intSpan_mono` and `mem_intSpan_of_isWt` are trivial membership facts.

## Integral weights of representations of `𝔤𝔩_n(ℂ)`

`diagOps σ p = σ(E_pp)`. The condition `intSpan (diagOps σ) = ⊤` is definitionally the Library's
`VermaGL.HasIntegralWeights σ`.

- `isWt_tmul`, `intSpan_tensorLie`: weights add on pure tensors, so tensor products of
  representations with integral weights have integral weights;
- `exists_wtBasis`: a finite-dimensional representation with integral weights has a basis of
  weight vectors (a linearly independent spanning subset of the weight vectors);
- `coord_comp_of_isWt`: for a weight basis, the coordinate functional of `b_i` composed with
  `H p` is `μ_i(p)` times the coordinate functional;
- `eq_sum_coord_smulRight`: `ψ = Σ_i b_i^* ⊗ ψ(b_i)` for a linear map `ψ` and a finite basis;
- `intSpan_homLie`: if `W` is finite-dimensional and `σ`, `τ` have integral weights, so does
  `homLie σ τ`. The map `b_i^* ⊗ x` has weight `ν - μ_i` when `x` has weight `ν`.
- `intSpan_trivial`: the zero representation on `ℂ` has integral weights;
- `intSpan_restrictLie`, `intSpan_restrictLie_of_le`: the restriction of `σ` to an invariant
  subspace contained in `intSpan (diagOps σ)` has integral weights (by `mem_span_wt_of_mem`).
