# Residue fields, prime elements and tame corestrictions of a common simple character

`SimpleCharacterResidueComparisonStatement` fixes a nonarchimedean local
field `F`, a finite-dimensional `F`-vector space `V`, an additive character
`ψ_F` with `IsBKAdditiveCharacter ψF`, and a lattice chain `L` representing
the hereditary order `𝔄` with radical `𝔓`. It takes simple strata
`[𝔄,n,0,γ₁]` and `[𝔄,n,0,γ₂]` on `L` with the same depth-zero pairs,
`simpleCharacterPairs ψF S₁ 0 = simpleCharacterPairs ψF S₂ 0`. Write
`Eᵢ = F[γᵢ]` (`elementAlgebra`), `𝔬_{Eᵢ}` for `subfieldIntegers F Eᵢ`, and
`𝔅ᵢ = 𝔄 ∩ End_{Eᵢ}(V)` (`centralizerLattice L γᵢ 0`). The statement
asserts the following.

- **(A)** `𝔅₁ + 𝔓 = 𝔅₂ + 𝔓` as `𝒪_F`-submodules of `End_F(V)`.
- When both `Eᵢ` are fields, with their field structures `IsField.toField`:
  - **(i)** every element of `𝔬_{E₁}` is congruent modulo `𝔓` to an element of
    `𝔬_{E₂}`, and conversely. So the residue fields `k_{E₁}` and `k_{E₂}` have
    the same image in `𝔄/𝔓`.
  - **(ii)** there are prime elements `πᵢ` of `𝔬_{Eᵢ}` (`RingPrimeElement`) and a
    unit `u ∈ U¹(𝔄)` with `π₂ = π₁ u` in `End_F(V)`, so `π₁U¹(𝔄) = π₂U¹(𝔄)`.
  - **(iii)** there are tame corestrictions `sᵢ` on `End_F(V)` relative to `Eᵢ/F`
    such that, for every integer `k` and every `x ∈ 𝔓^{−(k+1)}`,
    `s₁(x) − s₂(x) ∈ 𝔓^{−k}`. Here both values are viewed in `End_F(V)`.

## Sources

Clauses (i)–(iii) are Lemma (5.2) of Bushnell and Kutzko, *Simple types in
GL(N): computing conjugacy classes* (1994), printed p. 132 (PDF p. 145), with
its proof on printed pp. 133–135 (PDF pp. 146–148). Literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`. The lemma
assumes `C(𝔄,0,γ₁) = C(𝔄,0,γ₂)`. Clause (ii) states
`π₁U¹(𝔄) = π₂U¹(𝔄)`, which is the existence of `u` above.

Clause (A) is the equality `𝔅_{β₁} + 𝔓 = 𝔅_{β₂} + 𝔓` that Bushnell and Kutzko
derive in the proof of BK93 (3.5.1). The source is *The admissible dual of
GL(N) via compact open subgroups* (1993), printed p. 117 (PDF p. 129),
literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. There it
follows from the intertwining (3.3.2) of a common simple character. Equal sets
of depth-zero pairs share a character, because these sets are nonempty by BK93
(3.3.21), printed p. 114. BK94 prove the equalities
`𝔔₁^k + 𝔓^{k+1} = 𝔔₂^k + 𝔓^{k+1}`, (5.8) on printed p. 134, inside the proof of
(5.2). They do so where `𝔄` is maximal among the orders normalized by `F[γ₁]`.
Clause (A) is the case `k = 0`, which the argument of BK93 (3.5.1) gives for
every `𝔄`.

This file states the proposition and does not prove it.
