# Covering simple-character classes: the fibre characters

This module states three inputs and derives `FibreTwistCoverAt` (Bushnell and Kutzko, *Simple
types in GL(N): computing conjugacy classes* (1994), (2.7) and the surjectivity in (1.8),
printed pp. 114, 120–121) from them.

Throughout, `[𝔄,n,k+1,γ]` is a simple stratum on the indexed lattice chain `L`, and a simple
refinement of it is a simple stratum `[𝔄,n,k,β]` on the same indexed chain `L` with
`β ≡ γ (mod 𝔓^{-(k+1)})`. The additive character `ψ_F` is trivial on `𝔭_F` and nontrivial on
`𝔬_F`.

* `CorestrictionScalarMod L γ e k` is a scalar congruence: whenever `F[γ]` is a field, every tame
  corestriction relative to `F[γ]/F` carries `e` to a scalar of `F[γ]` modulo `𝔓^{-k}`. When
  `e ∈ 𝔓^{-(k+1)}` and `[𝔄,n,k+1,γ]` is simple, this says that the derived stratum
  `[𝔅_γ,k+1,k,s(e)]` is equivalent to a stratum with a scalar coefficient, possibly null. The
  definition itself places no condition on `e`.
* `TwistDecompositionAt` (BK93 (3.3.18), (3.3.20)(ii)): for simple strata `[𝔄,n,k+1,γ]` and
  `[𝔄,n,k,β]` on the same indexed chain `L` with `β ≡ γ (mod 𝔓^{-(k+1)})`, the pairs of
  `Ĉ(𝔄,k,β)` are exactly the twists by `ψ_{β-γ}` of the pairs of `Ĉ(𝔄,k,γ)`: each pair on one
  side has the same subgroup as a pair on the other side, and on that common subgroup the two
  characters differ by `ψ_{β-γ}`. The simplicity of `[𝔄,n,k+1,γ]` is essential, since without
  it `Ĉ(𝔄,k,γ)` may be empty.
* `FibreCharacterAt` (the quotient of two extensions: BK94 p. 120 and an auxiliary step of the
  proof of (2.7), not its conclusion on derived strata): two pairs of `Ĉ(𝔄,k,γ)` with the same
  restriction to `U^{k+2}(𝔄)` have the same subgroup and differ by `ψ_e` with
  `e ∈ 𝔓^{-(k+1)}` and `CorestrictionScalarMod L γ e k`.
* `RefinementSimpleAt` (BK93 (2.2.8), (2.4.1), BK94 (1.8)): for a simple refinement `β` of `γ`
  and `e ∈ 𝔓^{-(k+1)}` with `CorestrictionScalarMod L γ e k`, some simple refinement `β'` of `γ`
  satisfies `β' ≡ β + e (mod 𝔓^{-k})`.

* `fibreTwistCoverAt_of`: a pair `P` of `Y(θ)` over `[𝔄,n,k,β]` is `ϑ_P ψ_{β-γ}`; then
  `ϑ_P = ϑ ψ_e`, and `β'` gives a pair of `Ĉ(𝔄,k,β')` equal to `P`, of the form `ϑ ψ_{β'-γ}`.
