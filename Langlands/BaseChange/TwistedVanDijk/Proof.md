# The twisted van Dijk formula

Module `Langlands.BaseChange.TwistedVanDijk.Proof`. `twistedVanDijk` proves
`TwistedVanDijkStatement.{u, v, uW}` (module `Langlands.BaseChange.TwistedVanDijkStatement`):
Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non
nulle* (2011), II.4.5, formula (2) (printed p. 86). For admissible representations `P i` of the
blocks `GL_{n_i}(E)` with σ-intertwiners `A i`, Haar measures `μG`, `μM`, `μU` of volume one on
`K = GL_n(𝒪_E)`, `M(𝒪_E)`, `U ∩ K`, the Haar probability `μK` on `K`, a test function `φ` on
`G = GL_n(E)` and a test function `ψ` on `M` with the values of the twisted constant term
`ψ(x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du`,

`twistedDistribution μG π ι(A) φ = twistedDistribution μM τ (A₁ ⊗ ⋯ ⊗ A_r) ψ`,

where `π = normalizedProductInduced B P`, `ι(A) = inducedSigmaIntertwiner σ B A`,
`τ = B.blockTensor P` and `A₁ ⊗ ⋯ ⊗ A_r = leviTensorIntertwiner σ B A`. The twisted
distributions are the finite-rank traces `trace(π(φ) ∘ ι(A))` and
`trace(τ(ψ) ∘ (A₁ ⊗ ⋯ ⊗ A_r))`. The proof follows the classical argument for van Dijk's
formula: compute the trace on a finite-dimensional space of fixed vectors and use the kernel
of the operator in the compact model.

## Helper result

`leviTensorIntertwiner_comp_integratedAction`: for a test function `ψ` on `M`,
`(A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(ψ ∘ σ) = τ(ψ) ∘ (A₁ ⊗ ⋯ ⊗ A_r)`, where `ψ ∘ σ` is the pullback of `ψ` along
the entrywise action of `σ` on `M`. After a linear form `Λ` is applied
(`Hecke.integratedAction_dual`), both sides are integrals over `M`; the intertwining relation
`(A₁ ⊗ ⋯ ⊗ A_r) τ(m) = τ(σ(m)) (A₁ ⊗ ⋯ ⊗ A_r)` and the invariance of `μM` under `σ`
(`map_leviAut_eq`) identify them.

## Proof of `twistedDistribution_inducedSigmaIntertwiner`

This theorem is the formula for given measures; `twistedVanDijk` equips `GL_n(E)` and `M` with
their Borel σ-algebras and applies it.

1. `exists_level` gives a level `K'` of `φ`. The space `W'` of `K'`-fixed vectors of `π` is
   finite-dimensional (admissibility of `π`, `isAdmissible_normalizedProductInduced`), and the
   range of `π(φ) ∘ ι(A)` lies in it, since `φ` is left invariant under `K'`
   (`Hecke.integratedAction_range_le_fixedVectors`). So the trace is the trace of the
   restriction to `W'` (`FiniteRankEnd.trace_eq_subspace`).
2. On `W'`, the operator factors as `S ∘ R`, where `R : W' → (K/K' → ⊗ W_i)` evaluates at the
   coset representatives, `ξ ↦ (x ↦ ξ(rep x))`, and `S` is `compactOperator` with values in
   `W'` (`compactOperator_mem_fixedVectors`). This is the kernel formula
   `eval_integratedAction_inducedSigmaIntertwiner`.
3. `trace(S ∘ R) = trace(R ∘ S)` (`FiniteRankEnd.trace_ofFactorization`), and `R ∘ S` is the
   block operator on `K/K' → ⊗ W_i` with entries
   `c (A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(k(rep x, rep y))`, `c = μK(K')`; each entry has finite rank because
   `τ(·)` of a test function has finite rank (`Character.finiteRankIntegratedAction`).
4. `FiniteRankEnd.trace_blockOperator`: the trace is the sum of the traces of the diagonal
   entries, which by linearity is the trace of
   `(A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(∑_x c k(rep x, rep x))`.
5. `sum_kernelValue_diag` and the hypothesis on `ψ` give `∑_x c k(rep x, rep x) = ψ ∘ σ`.
6. By the helper result, `(A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(ψ ∘ σ) = τ(ψ) ∘ (A₁ ⊗ ⋯ ⊗ A_r)`, whose trace is
   the Levi twisted distribution.

The proof uses the Haar normalizations only through `iwasawa_measure_eq` in the kernel formula.
