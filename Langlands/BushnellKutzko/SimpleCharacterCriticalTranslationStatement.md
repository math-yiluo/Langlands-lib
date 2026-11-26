# Critical translation of a simple refinement

`SimpleCharacterCriticalTranslationStatement` fixes a nonarchimedean local
field `F`, a finite-dimensional `F`-vector space `V`, an additive character
`ψ_F` with `IsBKAdditiveCharacter ψF`, a lattice chain `L` representing the
hereditary order `𝔄`, an integer `n` and a natural number `m`. It takes simple
strata `T₁ = [𝔄,n,m+1,γ₁]` and `T₂ = [𝔄,n,m+1,γ₂]` on `L` with
`simpleCharacterPairs ψF T₁ m = simpleCharacterPairs ψF T₂ m`, that is,
`C(𝔄,m,γ₁) = C(𝔄,m,γ₂)` as sets of subgroup–character pairs. It also takes a
simple stratum `S₁ = [𝔄,n,m,β₁]` on `L` such that `c = β₁ − γ₁` lies in
`𝔓^{−(m+1)}` (`L.endFiltration (-(m+1))`) and the critical exponent
`k₀(β₁,𝔄)` equals `−(m+1)`. The statement asserts that there is a simple
stratum `S₂ = [𝔄,n,m,β₂]` on `L` with `β₂ − (γ₂ + c) ∈ 𝔓^{−m}`. In other
words, the stratum `[𝔄,n,m,γ₂ + c]` is equivalent to a simple stratum.

The condition `k₀(β₁,𝔄) = −(m+1)` says that `[𝔄,n,m+1,β₁]` is not simple. In
the opposite case BK94 deduce (2.11) directly from BK93 (3.5.9).

## Source

Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), §5, printed pp. 132–133 (PDF pp. 145–146), literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`. In the
proof of the Translation Principle (2.11), for `[𝔄,n,m+1,β₁]` not simple and
`β₁ = γ₁ + c`, Lemma (5.3) shows that the derived stratum
`[𝔅₂,m+1,m,s₂(c)]` over `F[γ₂]` is nonsplit fundamental. Then (5.5)–(5.6)
show that it is equivalent to a simple stratum. The text continues: "Thus the
stratum `[𝔄,n,m,γ₂+c]` is equivalent to a simple stratum `[𝔄,n,m,β₂]`". This is
the conclusion stated here.

## Derivation of the hypothesis

BK94 assume `C(𝔄,0,γ₁) = C(𝔄,0,γ₂)`. They obtain it from equality at depth
`m+1` with Bushnell and Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), (3.5.9), printed p. 121, literature ID
`bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`. The
statement here assumes equality at depth `m`. BK93 (3.5.9) at levels
`m, m−1, …, 1` replaces `γ₁` by an element `γ₁*` with `γ₁* − γ₁ ∈ 𝔓^{−m}` and
`C(𝔄,0,γ₁*) = C(𝔄,0,γ₂)`. The strata `[𝔄,n,m,γ₁]` and `[𝔄,n,m,γ₁*]` are simple
and equivalent, so `k₀(γ₁*,𝔄) = k₀(γ₁,𝔄)` by BK93 (2.4.1)(ii)(a), printed
p. 65. Hence `[𝔄,n,m+1,γ₁*]` is simple and equivalent to `[𝔄,n,m+1,β₁]`. The
argument of BK94 §5 for `γ₁*` and `c* = β₁ − γ₁*` gives a simple
`[𝔄,n,m,β₂]` equivalent to `[𝔄,n,m,γ₂ + c*]`. Since `c* − c ∈ 𝔓^{−m}`, this
stratum is also equivalent to `[𝔄,n,m,γ₂ + c]`.

This file states the proposition and does not prove it.
