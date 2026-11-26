# Reduction of the Translation Principle

`SimpleCharacterTranslationReductionStatement` is the implication from five
propositions to `SimpleCharacterTranslationStatement`, the Translation
Principle of Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy
classes* (1994), (2.11), printed p. 123. The five propositions are:

- `SimpleCharacterCriticalTranslationStatement`, the conclusion of BK94 (5.3)–(5.6);
- `SimpleCharacterLoweringStatement`, BK93 (3.5.9);
- `SimpleCharacterRestrictionStatement`, BK93 (3.2.4)–(3.2.5), (3.3.18), (3.3.21);
  only its critical-approximation clause (c), the twist formula (3.3.18), is used;
- `SimpleCharacterChoiceStatement`, BK93 (3.3.20);
- `PureStratumSimpleApproximationStatement`, BK93 (2.4.1)(i), used through
  `Stratum.exists_exact_definingSequenceChoice` to supply defining sequences.

The theorem `simpleCharacterTranslationReduction` proves the implication.

## Proof

The proof works with the sets of pairs `simpleCharacterPairs ψF S m`. It uses
the following auxiliary facts.

1. **Change of first index.** Two simple strata with the same chain, level and
   element have the same pairs at every depth (`simpleCharacterPairs_congr` in
   the module `Langlands.BushnellKutzko.SimpleCharacterPairsReindex`).
2. **One defining sequence suffices** (proved in this module). By the first clause of
   `SimpleCharacterChoiceStatement`, the pairs of a simple stratum with
   nonnegative index are those of any one of its defining sequences.
3. **Twist by an upper stratum** (proved in this module). Let `S = [𝔄,n,m,β]` and
   `T = [𝔄,n,m+1,γ]` be simple on the same chain with `β − γ ∈ 𝔓^{−(m+1)}`.
   Then the depth-`m` pairs of `S` are the pairs `(H, θ ψ_{β−γ})` for the
   depth-`m` pairs `(H, θ)` of `T`. If `k₀(β,𝔄) = −(m+1)`, then `T` is a
   critical approximation of `S`. The bijection of clause (c) of
   `SimpleCharacterRestrictionStatement` gives the formula in both directions.
   Otherwise `[𝔄,n,m+1,β]` is simple. Its pairs equal those of `S` by fact 1,
   and the second clause of `SimpleCharacterChoiceStatement` gives the formula.
   The second clause also shows that equivalent simple strata at level `m+1`
   have the same depth-`(m+1)` pairs. Indeed, `ψ_b` is trivial on
   `U^{m+2}(𝔄)` for `b ∈ 𝔓^{−(m+1)}` (`elementCharacter_eq_one_of_depth`).

Let `T₁ = [𝔄,n,m+1,γ₁]`, `T₂ = [𝔄,n,m+1,γ₂]` and `S₁ = [𝔄,n,m,β₁]` be as in
the Translation Principle. Since `S₁` is simple, `k₀(β₁,𝔄) < −m`.

- **Case `k₀(β₁,𝔄) < −(m+1)`.** Then `R₁ = [𝔄,n,m+1,β₁]` is simple and
  equivalent to `T₁`. By fact 3, `R₁` and `T₂` have the same depth-`(m+1)`
  pairs. `SimpleCharacterLoweringStatement` gives a simple
  `T₂' = [𝔄,n,m+1,β₂]` equivalent to `T₂`, with the same depth-`m` pairs as
  `R₁`. Take `S₂ = [𝔄,n,m,β₂]`. Then `β₂ − γ₂ ∈ 𝔓^{−(m+1)}`. By fact 1, the
  depth-`m` pairs of `S₂` and `T₂'` agree, and so do those of `R₁` and `S₁`.
- **Case `k₀(β₁,𝔄) = −(m+1)`.** `SimpleCharacterLoweringStatement` gives a
  simple `T₁' = [𝔄,n,m+1,γ₁']` equivalent to `T₁`, with the same depth-`m`
  pairs as `T₂`. Put `c = β₁ − γ₁' ∈ 𝔓^{−(m+1)}`.
  `SimpleCharacterCriticalTranslationStatement` gives a simple
  `S₂ = [𝔄,n,m,β₂]` with `β₂ − (γ₂ + c) ∈ 𝔓^{−m}`, so `β₂ − γ₂ ∈ 𝔓^{−(m+1)}`.
  By fact 3, the depth-`m` pairs of `S₂` are those of `T₂` twisted by
  `ψ_{β₂−γ₂}`. The pairs of `S₁` are those of `T₁'` twisted by `ψ_c`. Their
  domains lie in `U^{m+1}(𝔄)`, where `ψ_{β₂−γ₂} = ψ_c ψ_{β₂−γ₂−c}` and the
  last factor is trivial. Hence `S₂` and `S₁` have the same depth-`m` pairs.

## Sources

Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), (2.11), printed p. 123 (PDF p. 136), and §5, printed pp. 132–133
(PDF pp. 145–146), literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
The noncritical case is the remark "If `[m+1,β₁]` is itself simple, the
assertion follows from [BK1] (3.5.9)" on p. 132. In the critical case, the
character comparison uses the twist formula of BK93 (3.3.18). BK94 phrase it
as `θ = ϑψ_c ∈ C(𝔄,m,β₂)`.

Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (2.4.1)(i), (3.3.18), (3.3.20) and (3.5.9), printed pp. 65, 112, 113
and 121, literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
