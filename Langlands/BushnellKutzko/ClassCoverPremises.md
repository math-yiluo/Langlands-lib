# Covering simple-character classes: restriction, transport and nonemptiness

This module derives three inputs of `ClassCoverInduction` from Library statements about
simple characters, and states the remaining input. Throughout, `ψ_F` is an additive character of
`F` that is trivial on `𝔭_F` and nontrivial on `𝔬_F` (`IsBKAdditiveCharacter`); the theorems
below that use a Library statement about simple characters take this as a hypothesis, while the
combinatorial lemmas `simpleCharacters_cons_of_le_depth`, `exists_pair_mem_succ` and
`pair_mem_simpleCharacterPairsAt_succ` hold for every additive character.

* `Stratum.DefiningSequenceChoice.reindexSimple` moves a defining sequence (BK93 (2.4.2)) to a
  simple stratum with the same order, level and element and another index, keeping the
  later terms; its tail is unchanged.
* `simpleCharacterPairs_nonempty`: for a simple stratum `[𝔄,n,m,β]` with `m ≥ 0`, `Ĉ(𝔄,m,β)` is
  nonempty. The proof takes a defining sequence from `PureStratumSimpleApproximationStatement`
  and applies the last clause of `SimpleCharacterRestrictionStatement`, which says that the set
  of simple characters at every index `m < n` is nonempty. In BK93 this nonemptiness (announced
  on printed p. 98 and obtained with (3.3.18)) comes from the high-index singleton (3.2.4), the
  critical twist (3.3.18), and the surjectivity of restriction from each index onto the next
  (3.3.21), which carries nonemptiness downward. Proposition (3.2.5), on the image of restriction
  to index `⌊r/2⌋` and its fibres, is not used here.
* `exists_pair_mem_succ`: let `k + 1 < n`, let `[𝔄,n,k,β]` be a simple stratum on `L` and fix
  a defining sequence for it. A character at index `k + 1` computed using this defining sequence
  (an element of `simpleCharacters` at index `k + 1` for the element `β` and the tail of the
  sequence) is, as a pair, an element of `Ĉ(𝔄,k+1,γ)` for a simple stratum `[𝔄,n,k+1,γ]` on
  `L` with `γ ≡ β (mod 𝔓^{-(k+1)})`. If `[𝔄,n,k+1,β]` is simple then `γ = β`; otherwise
  `k + 1` is the critical depth of `β` and `γ` is the next element of the defining sequence, by
  the definition of `simpleCharacters`. This lemma holds for every additive character `ψ_F` and
  uses no Library statement about simple characters. Its corollary
  `pair_mem_simpleCharacterPairsAt_succ` places the pair in the union `S^{k+1}_n(𝔄)`.
* `exists_restrict_mem_succ` (BK93 (3.3.21)): for `ψ_F` as above, `k + 1 < n` and a simple
  stratum `[𝔄,n,k,β]` on `L`, the restriction of a pair of `Ĉ(𝔄,k,β)` to `U^{k+2}(𝔄)` is a pair
  of `Ĉ(𝔄,k+1,γ)` for a simple stratum `[𝔄,n,k+1,γ]` on `L` with `γ ≡ β (mod 𝔓^{-(k+1)})`. The
  restriction clause of `SimpleCharacterRestrictionStatement` (BK93 (3.3.21)) gives a character
  of the next index computed using the same defining sequence, the carrier clause of
  `SimpleStratumGroupPropertiesStatement` (BK93 (3.1.14)) identifies its group with the
  intersection of the original group with `U^{k+2}(𝔄)`, and `exists_pair_mem_succ` finishes.
* `pairRestrictionAt` (BK94 (2.2)): under the same hypotheses on `ψ_F` and `k`, and the same two
  Library statements, restriction to `U^{k+2}(𝔄)` maps the union `S^k_n(𝔄)` of the sets
  `Ĉ(𝔄,k,β)` over simple strata `[𝔄,n,k,β]` on `L` into the union `S^{k+1}_n(𝔄)` at the
  successor depth; this is `PairRestrictionAt`, a consequence of `exists_restrict_mem_succ`.
* `simpleCharacterPairs_subset_of_sub_mem`: for simple strata `[𝔄,n,m,β]` and `[𝔄,n,m,β']` on the
  same indexed chain with `β' ≡ β (mod 𝔓^{-m})`, `Ĉ(𝔄,m,β) ⊆ Ĉ(𝔄,m,β')`; by symmetry `Ĉ(𝔄,m,β)`
  depends only on the equivalence class of `[𝔄,n,m,β]` (BK94 p. 118). It follows from the twist
  clause of `SimpleCharacterChoiceStatement` (BK93 (3.3.20)(ii), with `ℓ = m`): the twisting
  character `ψ_{β'-β}` is trivial on `U^{m+1}(𝔄)`.
* `simpleCharacterPairs_conj_mem`: for finite-dimensional `V` and simple strata `[𝔄,n,m,β]`,
  `[𝔄,n,m,β']` on `L`, conjugation by `u ∈ U(𝔄)` carries `Ĉ(𝔄,m,β)` into `Ĉ(𝔄,m,β')` whenever
  `β' ≡ u⁻¹ β u (mod 𝔓^{-m})`, from `SimpleCharacterConjugationStatement`
  and the previous item; `LatticeChain.linearEquivMap_unit` shows that `u` fixes the chain.
* `SimpleCharacterFibreInjectionStatement` states `FibreInjectionAt` for every finite-dimensional
  `V`, every `ψ_F` as above, every lattice chain and every depth `k` with `k + 1 < n` (BK94
  (2.7)–(2.10), upper half), and
  `simpleCharacterClassCover_of_fibreInjection` proves `SimpleCharacterClassCoverStatement`
  from it and from `PureStratumSimpleApproximationStatement`,
  `SimpleCharacterConjugationStatement`, `SimpleCharacterChoiceStatement`,
  `SimpleStratumGroupPropertiesStatement` and `SimpleCharacterRestrictionStatement`.

Sources: Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (2.4.2), (3.1.14), (3.2.4), (3.3.18), (3.3.20), (3.3.21); Bushnell and Kutzko, *Simple types in
GL(N): computing conjugacy classes* (1994), p. 118 and (2.2).
