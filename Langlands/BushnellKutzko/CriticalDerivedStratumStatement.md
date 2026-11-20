# The derived stratum at the critical level

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Theorem (2.4.1)(iii),
printed p. 65 (PDF p. 77). The proof is on printed pp. 66–75.

`CriticalDerivedStratumStatement` is an unproved proposition definition.
It quantifies over every nonarchimedean local field `F` and
finite-dimensional `F`-vector space `V`, in independent universes.

Let `S = [𝔄,n,r,β]` be a pure stratum at its critical level, that is,
`k₀(β,𝔄) = −r`. Let `T = [𝔄,n,r,γ]` be a simple stratum with the same
lattice chain and integers `n`, `r`, and suppose `S` is equivalent to `T`.
Then `T.HasSimpleDerivedStratum (β − γ)` holds.

The published predicate `Stratum.HasSimpleDerivedStratum` states the
source's conclusion. For every tame corestriction `s_γ` relative to the
actual field `F[γ]/F`, the derived stratum `[𝔅_γ,r,r−1,s_γ(β−γ)]` exists
(with `𝔅_γ` the centralizer order, built from the original underlying
lattices) and is equivalent to a simple stratum over `F[γ]`.

The critical-level condition is written `criticalExponent S.chain S.b =
−S.r` in `WithBot ℤ`. It excludes the scalar case `k₀ = −∞` without a
separate finiteness hypothesis.

This is exactly the third conjunct of the published
`StratumApproximationStatement` (T7), stated on its own. The source's common
hereditary order is represented by one fixed lattice-chain presentation, via
`T.chain = S.chain`.
