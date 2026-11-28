# The truncated limit of Lapid §8 for one pair of parabolic subgroups

Module `Langlands.Global.LocalWavePacketPairLimit`. It is a helper module for the proof
`Langlands.Global.truncatedWavePacketStandardization` (module
`Langlands.Global.LocalWavePacketStandardReductionProof`) and contains no statement of its own.

## Definitions

- `TruncatedWavePacketLimitConclusion Λ Θ Θ' rhs`: the conclusion of the limit of Lapid 2011, §8
  (the sufficient condition obtained from Lemma 9) for two functions `Θ`, `Θ'` on `G(𝔸)`, a
  truncation operator `Λ j` (`j : ℕ`) on functions on `G(F) \ G(𝔸)` and a limit value `rhs`:
  `y ↦ Θ(y.out)` and `y ↦ Θ'(y.out)` are measurable and bounded on compact sets, their truncations
  are eventually square integrable with bounded norms, and `(Λ j Θ, Λ j Θ')` tends to `rhs`. These
  are verbatim the nine conjuncts of the conclusion of
  `TruncatedWavePacketSectionSomeCompactLimitStatement` (module
  `Langlands.Global.LocalWavePacketSomeCompactReduction`), with `trunc j f = Λ j f`.
- `TruncatedWavePacketPairLimit K Λ p iU l hK Reg p' iU' l' π' hK' Reg'`: for one compact subgroup
  `K` with `P(𝔸)K = P'(𝔸)K = G(𝔸)`, one truncation operator `Λ` and regularity predicates `Reg` on
  the parameters of `P` and `Reg'` on those of `P'`, every datum of
  `TruncatedWavePacketSectionSomeCompactLimitStatement` (square integrable induced forms, entire
  coefficients `b`, continuations `E` agreeing with Eisenstein series on `Reg`-regular parameters,
  smooth compactly supported coefficients `c`, representatives of `Ω(P, P')`, expansions of the
  intertwining operators on `Reg`-regular parameters, an Iwasawa-compatible Haar measure on
  `M'(𝔸)` and a weight `β'`) satisfies `TruncatedWavePacketLimitConclusion` with the right side of
  Lapid's formula (4). The order of the binders is that of the target statement.

The predicate isolates the part of the target statement that is transported between parabolic
subgroups; the compact subgroup and the truncation are fixed.

## Lemma

- `TruncatedWavePacketPairLimit.mono_reg`: if every `Reg₁`-region contains a `Reg`-region (for
  every bound `R₁` there is `R` with `Reg R λ → Reg₁ R₁ λ`), and likewise for `Reg'`, `Reg'₁`, then
  the limit for `Reg`, `Reg'` gives the limit for `Reg₁`, `Reg'₁`. Proof: the hypotheses that use
  the regularity predicates assert identities on a region `{λ : Reg₁ R₁ λ}`; such an identity
  holds on the smaller region `{λ : Reg R λ}`, so the data satisfy the hypotheses for `Reg`, `Reg'`.
