# Adjoint preimages in `𝔍` and the group `J^m` from intertwining

This module proves two facts about a simple stratum `[𝔄,n,r₀,β]` over a
nonarchimedean local field `F`, with critical depth `r = −k₀(β,𝔄)` (the Lean
`finiteCriticalDepth`, which takes the value `n` when `β` is scalar). The lattice
`𝔍(β,𝔄)` and the groups `J^m(β,𝔄)`, `H^m(β,𝔄)` are those of `simpleJLattice`,
`simpleJGroup` and `simpleHGroup`, computed from a defining sequence.

Source: Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`:
the definition (3.1.8), printed p. 90 (PDF p. 102); the group properties
(3.1.15), printed p. 95 (PDF p. 107); the intertwining formula (3.3.2) and the
Remark after it, printed p. 105 (PDF p. 117); and the use of these facts in the
proof of (3.5.9), printed p. 121 (PDF p. 133).

## Adjoint preimages

`adjointLattice_le_simpleJLattice` states: if `2k ≤ r`, then every `x ∈ 𝔄` with
`βx − xβ ∈ 𝔓^{−k}` lies in `𝔍(β,𝔄)`, for every defining sequence. In the notation
of BK93 (1.4.3) this is `𝔑_{−k}(β,𝔄) ⊆ 𝔍(β,𝔄)`. For `k = 0` it is the inclusion
`𝔑_0(β,𝔄) ⊆ 𝔍(β,𝔄)`.

The proof is an induction along the defining sequence. Let `−d` be the critical
exponent of the current term `b`, so `d ≥ 2k`. The exactness statement
`exists_commute_sub_mem` writes `x = y + z` with `y` commuting with `b` and
`z ∈ 𝔓^{d−k}`. Then `y ∈ 𝔅_b`, which is contained in `𝔍(b)`. The next term `b'`
satisfies `b' − b ∈ 𝔓^{−d}`, so the commutator of `z` with `b'` again lies in
`𝔓^{−k}`, and the induction hypothesis puts `z` into `𝔍(b')`. Since `d − k` is at
least the cutoff `⌊(d+1)/2⌋`, the element `z` also lies in `𝔓^{⌊(d+1)/2⌋}`, which
is the term of `𝔍(b)` built from `𝔍(b')`. For the last term, with critical
exponent `−n`, the same splitting puts `z` into `𝔓^{n−k} ⊆ 𝔓^{⌊(n+1)/2⌋}`. A scalar
last term has centralizer `𝔄`. The depth bounds come from the strictly increasing
indices of the defining sequence: every critical depth along it is at least `r`,
and `finiteCriticalDepth_le_level` gives `r ≤ n`.

## The outer factor of the intertwining formula

The Remark after (3.3.2) states that `𝔔^{r−m}𝔑(β) ⊆ 𝔍^{⌊(r+1)/2⌋}(β)` when
`m ≤ ⌊r/2⌋`. `simpleCharacterIntertwiningFactor_eq_simpleJLayer` proves this for
nonscalar `β` and `2m ≤ r`: a product `az` with `a ∈ 𝔔^{r−m}` and `z ∈ 𝔑_{−r}` lies
in `𝔓^{r−m} ⊆ 𝔓^{⌊(r+1)/2⌋}`, and its commutator with `β` is `a(βz − zβ) ∈ 𝔓^{−m}`.
The previous result with `k = m` puts `az` into `𝔍(β)`. Hence the outer factor
`simpleCharacterIntertwiningFactor` at depth `m` is the set of units `g` with
`g − 1 ∈ 𝔍^{⌊(r+1)/2⌋}`.

## `J^m` as an intersection

`simpleJGroup_eq_selfIntertwining_inter` takes `SimpleStratumGroupPropertiesStatement`
and `SimpleCharacterIntertwiningStatement` as hypotheses. For a simple stratum
`[𝔄,n,0,β]`, a depth `m` with `1 ≤ m < n` and `2m ≤ r`, and any `χ ∈ C(𝔄,m,β)`, it
proves

`J^m(β,𝔄) = I_G(χ) ∩ U^m(𝔄)`.

For nonscalar `β` the intertwining formula and the previous result give
`I_G(χ) = J^t B_β^× J^t` with `t = ⌊(r+1)/2⌋ ≥ m`, using the exact carrier of `J^t`.
An element `y₁ b y₂` of this double coset that lies in `U^m(𝔄)` has
`b ∈ B_β^× ∩ U^m(𝔄)`. This `b` normalizes `J^t`, so the element lies in
`U^m(𝔅_β) J^t`, which is `J^m` by the product formula of (3.1.15). Conversely
`U^m(𝔅_β) J^t` is contained in the double coset. For scalar `β` the outer factor is
trivial, the centralizer is all of `G` and `J^m = U^m(𝔄)`.
