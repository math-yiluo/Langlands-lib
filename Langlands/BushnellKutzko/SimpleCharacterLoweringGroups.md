# The groups `H^m` of simple strata with equal simple character pairs

`SimpleCharacterLoweringGroupsReductionStatement` is the first assertion of
Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (3.5.9), printed p. 121 (PDF p. 133), as an implication from five published
statements: `SimpleStratumGroupPropertiesStatement` ((3.1.14)–(3.1.15)),
`SimpleCharacterRestrictionStatement` ((3.2.4), (3.2.5), (3.3.18), (3.3.21)),
`SimpleCharacterChoiceStatement` ((3.3.20)), `SimpleCharacterIntertwiningStatement`
((3.3.2), (3.3.17)) and `SimpleCharacterPairingStatement` ((3.4.1)). The literature
ID is `bushnell-kutzko-1993-admissible-dual-gln`, with SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

Its conclusion concerns a nonarchimedean local field `F`, an `F`-vector space `V`,
an additive character `ψ_F` satisfying `IsBKAdditiveCharacter`, a lattice chain `L`
with hereditary order `𝔄`, an integer `n` and a natural number `m ≥ 1`. For two
simple strata `[𝔄,n,m,β₁]` and `[𝔄,n,m,β₂]` on `L` with
`simpleCharacterPairs ψ_F S m = simpleCharacterPairs ψ_F T m`, it asserts
`H^m(β₁,𝔄) = H^m(β₂,𝔄)` for every pair of defining sequences. Unlike
`SimpleCharacterLoweringStatement`, the conclusion does not assume `V`
finite-dimensional, since a lattice chain already forces this. The module proves the
statement in `simpleCharacterLoweringGroupsReduction`.

## Bookkeeping of pairs

`characterPair_mk_eq_iff` identifies equality of pairs `(H, θ)` with equality of the
subgroups and pointwise agreement of the characters. `characterPair_image_eq_iff`
does the same for the images of a nonempty character set and another character set:
equality means equal domains and a two-sided correspondence
(`CharacterSetTwistCorrespondence` with trivial twist). With the first clause of the
choice statement, `simpleCharacterPairs_eq_image` shows that `simpleCharacterPairs`
is the image of the simple characters of any single defining sequence.
`simpleCharacters_correspond_of_pairs_eq` adds the nonemptiness clause of the
restriction statement. Equal sets of pairs therefore give, for any defining
sequences, equal domains `H^{m+1}` and characters `θ₀ ∈ C(𝔄,m,β₁)`,
`φ₀ ∈ C(𝔄,m,β₂)` that agree pointwise.

## The proof

Write `m = i + 1`. If `⌊n/2⌋ ≤ i`, the proved `simpleCharacterHighIndex` gives
`H^m(β_j) = U^m(𝔄)` for both strata.

Otherwise `simpleHGroup_eq_of_common_character_of_lt_half` applies. Its route
differs from the source, which compares additive closures of intertwining sets and
uses the jump sequences of (3.5.4). Here core approximations replace these steps:

1. The adjacent restriction clause lifts `θ₀` and `φ₀` to `θ ∈ C(𝔄,i,β₁)` and
   `φ ∈ C(𝔄,i,β₂)`.
2. `exists_simpleCharacterCore_with_depth_bound` gives for each `β_j` a simple stratum
   `δ_j` on the same chain and level with `2m ≤ r(δ_j)` and
   `β_j − δ_j ∈ 𝔓^{1−2m}`. It also gives `H^m(β_j) = H^m(δ_j)` and characters
   `θ' ∈ C(𝔄,i,δ₁)`, `φ' ∈ C(𝔄,i,δ₂)` with `θ = θ'ψ_{β₁−δ₁}` and
   `φ = φ'ψ_{β₂−δ₂}` on `H^m`. `SimpleCharacterCore.domain_eq_of_le` gives
   `H^{m+1}(β_j) = H^{m+1}(δ_j)`.
3. On `H^{m+1}` the restrictions satisfy `θ'ψ_{β₁−δ₁} = φ'ψ_{β₂−δ₂}`. Both
   coefficients lie in `𝔓^{1−2m}`. By `elementCharacter_conj_eq_of_mem`, conjugation
   by `g ∈ U^m(𝔄)` leaves `ψ_c` unchanged on `U^{m+1}(𝔄)` for `c ∈ 𝔓^{1−2m}`.
   Therefore `mem_characterSelfIntertwining_of_relation` shows that the restrictions
   of `θ'` and `φ'` to `H^{m+1}` have the same intertwining elements in `U^m(𝔄)`.
4. `simpleJGroup_eq_selfIntertwining_inter` identifies `J^m(δ_j)` with that set, so
   `J^m(δ₁) = J^m(δ₂)`.
5. `mem_simpleHGroup_iff_commutator` restates the nondegeneracy of the commutator
   pairing: an element `x ∈ J^m(δ₁)` lies in `H^m(δ₁)` exactly when `θ'[x,y] = 1`
   for all `y ∈ J^m(δ₁)`, and similarly for `δ₂` and `φ'`. By (3.1.15) the
   commutators lie in `H^{2m}(δ_j) ⊆ H^{m+1} ∩ U^{2m}(𝔄)`. There
   `ψ_{β₁−δ₁}` and `ψ_{β₂−δ₂}` are trivial (`elementCharacter_eq_one_of_mem_endFiltration`,
   which uses the proved additive duality), so `θ'` and `φ'` agree on these commutators.
   Hence `H^m(δ₁) = H^m(δ₂)`, and so `H^m(β₁) = H^m(β₂)`.

The case `m ≤ ⌊r/2⌋` of the source, where `J^m(β₁) = J^m(β₂)` comes from the
intertwining of a common character and `H^m` from the pairing (3.4.1), is the
special case in which each `δ_j` can be taken to be `β_j`.

The remaining helpers are `elementCharacter_ne_zero` (values of `ψ_b` are nonzero)
and `simpleCharacters_restriction_image`, the adjacent restriction clause for a stratum
at a nonnegative index.
