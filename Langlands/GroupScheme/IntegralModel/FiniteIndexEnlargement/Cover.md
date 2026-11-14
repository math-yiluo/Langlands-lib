# Covering a Hopf algebra by translates of an element with unit counit

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement`. It contains no
definitions. Its results are derived for this proof.

## Linear algebra

Let `R` be a local ring, `ϖ ∈ R`, `M` an `R`-module with `ϖ • m = 0` for all `m`, and `C` an
`R`-module with a family of linear forms `σ z : C →ₗ[R] R` (`z : Z`). Assume the forms detect
divisibility by `ϖ`: if `σ z c` lies in the maximal ideal for every `z`, then `c = ϖ • c'` for
some `c'`.

`eq_zero_of_forall_rid_lTensor`: if `t : M ⊗[R] C` has `rid ((id ⊗ σ z) t) = 0` in `M` for
every `z`, then `t = 0`.

Proof: write `t = ∑_{i < n} mᵢ ⊗ cᵢ` (`TensorProduct.exists_sum_tmul_eq`) and induct on `n`.

- If every `σ z cᵢ` lies in the maximal ideal, each `cᵢ` is divisible by `ϖ`, so each term is
  `ϖ mᵢ ⊗ cᵢ' = 0`.
- Otherwise some `σ z c_j` is a unit `u`. The relation `∑ σ z (cᵢ) mᵢ = 0` expresses `m_j` in
  terms of the other `mᵢ`. Substituting rewrites `t` as a sum of `n` terms
  `mᵢ ⊗ (cᵢ - u⁻¹ σ z (cᵢ) c_j)`, and the induction hypothesis applies.

`rid_lTensor_sum` is the evaluation of the contraction on a finite sum.

## Hopf algebras

Let `C` be a commutative Hopf algebra over the local ring `R`, and let `I` be an ideal of `C`.

- `rid_lTensor_rTensor_mkₐ`: reducing the left factor modulo `I` commutes with contracting the
  right factor against a linear form.
- `mul'_map_rTensor_mkₐ`: reducing modulo `I` commutes with `m ∘ (id ⊗ S)`, where `S` is the
  antipode.

`span_insert_pointTrans_eq_top` (**covering lemma**): let `τ z : C →ₐ[R] R` be a family of
integral points detecting divisibility by `ϖ` as above, and let `e : C` have unit counit. Then
`ϖ` and the translates `pointTrans (τ z) e` generate the unit ideal of `C`.

Proof: let `I` be the ideal they generate and `M = C ⧸ I`; then `ϖ` kills `M`. Let
`t ∈ M ⊗ C` be the image of `Δ e`. Contracting `t` with `τ z` gives the class of
`pointTrans (τ z) e`, which is zero in `M`. By the linear-algebra lemma, `t = 0`. Applying
`m ∘ (id ⊗ S)` to `Δ e` gives `ε(e) · 1` (`HopfAlgebra.mul_antipode_lTensor_comul_apply`), so
the class of `ε(e) · 1` in `C ⧸ I` is zero. Since `ε(e)` is a unit, `I = ⊤`.

## Provenance

This is a Hopf-algebraic form of the fact that the translates of a neighbourhood of the identity
cover the group. It replaces a covering argument on the special fibre, and no basis of the
residue field is needed. It was derived for this formalization.
