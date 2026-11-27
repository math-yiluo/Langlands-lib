# Covering simple-character classes: the induction on the depth

This module reduces `SimpleCharacterClassCoverStatement` (Bushnell and Kutzko,
*Simple types in GL(N): computing conjugacy classes* (1994), (2.3), printed p. 119) to
statements about one depth at a time.

## Pairs

For a group `G`, `CharacterPair.conj` is the conjugation of the Library, with
`(P.conj x).1 = x⁻¹ P.1 x` and `(P.conj x).2 (y) = P.2 (x y x⁻¹)`
(`CharacterPair.mem_conj_fst`, `CharacterPair.conj_snd_apply`). The module proves
`conj_one`, `conj_conj`, and that `CharacterPair.AreConjugateBy U` is reflexive,
symmetric and transitive for a subgroup `U`. `CharacterPair.restrict P K` is the
restriction of `P` to `P.1 ⊓ K`; it commutes with conjugation by elements normalizing
`K` (`restrict_conj`).

`LatticeChain.conj_mem_endFiltration` and `LatticeChain.conj_mem_unitFiltration_iff` show
that `U(𝔄)` preserves each `𝔓^j` and normalizes each `U^k(𝔄)`.
`unitConjCongr L k β γ` says that `γ ≡ u⁻¹ β u (mod 𝔓^{-k})` for some `u ∈ U(𝔄)`; it is an
equivalence relation, weaker for larger `k`.

## The reduction

Here `F` is a nonarchimedean local field, `V` an `F`-vector space, `L` a lattice chain in `V`
with hereditary order `𝔄`, `n ∈ ℤ`, and `ψF` an additive character of `F`. Where a theorem uses
that `ψ_F` is trivial on `𝔭_F` and nontrivial on `𝔬_F` (`IsBKAdditiveCharacter`), this is said
below.

* `ClassCoverAt ψF L n m` is the conclusion of `SimpleCharacterClassCoverStatement` for
  fixed data.
* `ClassInjectionAt ψF L n m`: a choice `κ` of a simple stratum for each pair of
  `S^m_n(𝔄)` such that the pair is `U(𝔄)`-conjugate to a pair of `Ĉ(𝔄,m,κ P)` and such that
  `κ P` and `κ Q` related by `unitConjCongr` forces `P` and `Q` to be conjugate.
* `classCoverAt_of_injection`: such a `κ`, the transport of `Ĉ(𝔄,m,β)` along
  `unitConjCongr`, and nonemptiness of `Ĉ(𝔄,m,β)` give `ClassCoverAt`. The function `Φ` is
  defined class by class: on a class of strata meeting the image of `κ` it takes a pair
  conjugate to the corresponding characters, otherwise any pair of a representative,
  transported to the stratum.
* `classInjectionAt_of_half_le`: for `⌊n/2⌋ ≤ m` and `ψ_F` as above, the Library's
  `simpleCharacterHighIndex` (BK93 (3.2.4)) gives `H^{m+1}(β,𝔄) = U^{m+1}(𝔄)` and the values `ψ_β`,
  so the stratum of a pair is injective on classes.
* `PairRestrictionAt` (restriction to `U^{m+2}(𝔄)` maps `S^m_n(𝔄)` into `S^{m+1}_n(𝔄)`,
  BK94 (2.2)) and `FibreInjectionAt` (BK94 (2.7)–(2.10)) are the inputs of the step
  `classInjectionAt_step`. `FibreInjectionAt` says: for each simple stratum `[𝔄,n,m+1,γ]` on
  `L` and each pair `θ` of `Ĉ(𝔄,m+1,γ)`, there is a choice `κ P` of a simple stratum
  `[𝔄,n,m,β]` on `L`, for the pairs `P` of `S^m_n(𝔄)` whose restriction to `U^{m+2}(𝔄)` is
  `U(𝔄)`-conjugate to `θ`, such that `β ≡ γ (mod 𝔓^{-(m+1)})`, `P` is `U(𝔄)`-conjugate to a pair
  of `Ĉ(𝔄,m,κ P)`, and for two such pairs `P`, `Q`, `κ P` and `κ Q` related by `unitConjCongr`
  force `P` and `Q` to be conjugate.
* `classInjectionAt_of_premises` is the downward induction on `m`, for `ψ_F` as above: from
  `PairRestrictionAt` and `FibreInjectionAt` at every `k` with `k + 1 < n` it gives
  `ClassInjectionAt` at every `m < n`. `classCoverAt_of_premises` is the resulting cover at a
  depth `m < n`, given also the transport and nonemptiness inputs of
  `classCoverAt_of_injection`.

The route differs from BK94, which builds bijections on classes: only an injection from
character classes into stratum classes is constructed, which is what the upper bound needs.
