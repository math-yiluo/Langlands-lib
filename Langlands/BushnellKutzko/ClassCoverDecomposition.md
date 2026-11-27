# Covering simple-character classes: twisting by `ψ_{β-γ}`

This module proves `TwistDecompositionAt`.

Throughout, `ψ_F` is an additive character of `F` that is trivial on `𝔭_F` and nontrivial on
`𝔬_F` (`IsBKAdditiveCharacter`), a hypothesis of both theorems.

`twist_correspondence`: let `[𝔄,n,k+1,γ]` and `[𝔄,n,k,β]` be simple strata on the same indexed
lattice chain (the hypothesis `T.chain = S.chain`), with `β ≡ γ (mod 𝔓^{-(k+1)})`. For any
defining sequences of the two strata, `H^{k+1}(β,𝔄) = H^{k+1}(γ,𝔄)` and the simple characters of
`β` at index `k` are exactly those of `γ` multiplied by `ψ_{β-γ}`.

* If `[𝔄,n,k+1,β]` is simple, this is the twist clause of `SimpleCharacterChoiceStatement`
  (Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
  (3.3.20)(ii)), applied to `[𝔄,n,0,β]` and `[𝔄,n,k+1,γ]`.
* Otherwise `k + 1` is the critical depth of `β`, `[𝔄,n,k+1,γ]` is a critical approximation of
  `[𝔄,n,0,β]`, and the critical-twist clause of `SimpleCharacterRestrictionStatement` (BK93
  (3.3.18)) gives a bijection of the character sets with the same twist.

`twistDecompositionAt` converts this into the statement on pairs, using
`PureStratumSimpleApproximationStatement` for the existence of defining sequences.
