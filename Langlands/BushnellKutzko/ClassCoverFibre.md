# Covering simple-character classes: the restriction fibres

This module reduces the fibre input `FibreInjectionAt` of `ClassCoverInduction` to two
statements, BK94 (2.7) with (1.8) and BK94 (2.8), following Bushnell and Kutzko, *Simple
types in GL(N): computing conjugacy classes* (1994), pp. 120–123. Throughout, `ψ_F` is an
additive character of `F` that is trivial on `𝔭_F` and nontrivial on `𝔬_F`
(`IsBKAdditiveCharacter`); every theorem below that concerns simple characters takes this as a
hypothesis.

* `transport_inter_nonempty` and `exists_eq_pair_of_transport` compare pairs whose characters
  lie in sets of characters of equal subgroups.
* `simpleCharacterPairs_eq_choiceImage_of_le` and `simpleCharacterPairs_eq_choiceImage`: for a
  simple stratum `[𝔄,n,r,β]` and `j ≤ r`, one defining sequence computes all of `Ĉ(𝔄,j,β)`
  (choice clause of `SimpleCharacterChoiceStatement`, BK93 (3.3.20)).
* `simpleCharacterPairs_subset_of_common`: for simple strata `[𝔄,n,j,β₁]` and `[𝔄,n,j,β₂]` on
  lattice chains with the same hereditary order `𝔄`, a common pair forces
  `Ĉ(𝔄,j,β₁) ⊆ Ĉ(𝔄,j,β₂)`, hence equality by symmetry (`SimpleCharacterCoherenceStatement`, BK93
  (3.5.8)).
* `exists_conj_simpleStratumAt`: a `U(𝔄)`-conjugate of a simple stratum is a simple stratum on
  the same chain (`SimpleCharacterConjugationStatement`).
* `exists_fibre_representative` is BK94 (2.10): for finite-dimensional `V`, `k + 1 < n`, a simple
  stratum `[𝔄,n,k+1,γ]` on `L` and `θ ∈ Ĉ(𝔄,k+1,γ)`, a pair of `S^k_n(𝔄)` whose restriction to
  `U^{k+2}(𝔄)` is `U(𝔄)`-conjugate to `θ` is `U(𝔄)`-conjugate to a pair of `Ĉ(𝔄,k,β)`, for a
  simple stratum `[𝔄,n,k,β]` on `L` with `β ≡ γ (mod 𝔓^{-(k+1)})`, whose restriction is `θ`. The proof conjugates, restricts, uses coherence
  and applies `SimpleCharacterTranslationStatement` (BK94 (2.11)).
* `fibrePairs` is the set `Y(θ)` of BK94 p. 120: for a simple stratum `[𝔄,n,k+1,γ]` on `L`, the
  pairs of the sets `Ĉ(𝔄,k,β)` over simple strata `[𝔄,n,k,β]` on `L` with
  `β ≡ γ (mod 𝔓^{-(k+1)})` whose restriction to `U^{k+2}(𝔄)` is `θ`. `FibreClassInjectionAt`
  (BK94 (2.9), upper half) chooses for each pair of `Y(θ)` such a stratum carrying a conjugate of
  the pair, injectively on classes, and
  `fibreInjectionAt_of_fibreClassInjection` derives `FibreInjectionAt` from it for
  finite-dimensional `V` and `k + 1 < n`.
* `exists_pair_restrict_eq`: for a simple stratum `[𝔄,n,k+1,γ]`, every pair of `Ĉ(𝔄,k+1,γ)`
  is the restriction to `U^{k+2}(𝔄)` of a pair of `Ĉ(𝔄,k,γ)` (BK93 (3.3.21)).
* `TwistConjugacyAt` and `FibreTwistCoverAt` are stated for a fixed extension `ϑ`;
  `fibreClassInjectionAt_of_twist` derives `FibreClassInjectionAt` from them.
  Here `[𝔄,n,k+1,γ]` is a simple stratum on `L` and `ϑ ∈ Ĉ(𝔄,k,γ)`.
  `TwistConjugacyAt` is BK94 (2.8), (ii) ⇒ (iii), in the case of twist coefficients
  `c_i = β_i - γ`: for simple strata `[𝔄,n,k,β_i]` on `L` with `β_i ≡ γ (mod 𝔓^{-(k+1)})`, if
  `β₂ ≡ u⁻¹ β₁ u (mod 𝔓^{-k})` for some `u ∈ U(𝔄)`, then the pairs `P_i ∈ Ĉ(𝔄,k,β_i)` on the
  subgroup of `ϑ` whose characters are `ϑ ψ_{β_i-γ}` are `U(𝔄)`-conjugate. Condition (ii)
  enters in the form used in BK94's proof, as `U(𝔄)`-conjugacy of the elements modulo
  `𝔓^{-k}`. `FibreTwistCoverAt` (BK94 (2.7) with the surjectivity in (1.8)) says that, for `θ`
  the restriction of `ϑ` to `U^{k+2}(𝔄)`, every pair of `Y(θ)` is `U(𝔄)`-conjugate to a pair of
  `Ĉ(𝔄,k,β)` on the subgroup of `ϑ` with character `ϑ ψ_{β-γ}`, for some simple stratum
  `[𝔄,n,k,β]` on `L` with `β ≡ γ (mod 𝔓^{-(k+1)})`.
