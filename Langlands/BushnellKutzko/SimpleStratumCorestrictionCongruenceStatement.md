# Corestriction congruence for equivalent simple strata

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, Theorem (2.4.1)(ii)(c),
printed p. 65 (PDF p. 77). The proof is on printed pp. 66–75.

`SimpleStratumCorestrictionCongruenceStatement` is an unproved proposition
definition. It quantifies over every nonarchimedean local field `F` and
finite-dimensional `F`-vector space `V`, in independent universes.

Let `S = [𝔄,n,r,γ₁]` and `T = [𝔄,n,r,γ₂]` be simple strata with the same
lattice chain and the same integers `n`, `r`, and suppose `S` is equivalent
to `T`. Let `h` be any witness that the actual generated algebra
`F[γ₁] = elementAlgebra S.b` is a field, and give it the corresponding field
structure. Then for every tame corestriction `s` relative to `F[γ₁]/F`
(the published `TameCorestriction 𝒪[F] F F[γ₁] V`) there is `δ ∈ F[γ₁]` with

`s(γ₁ − γ₂) − δ ∈ 𝔓^{1−r}`.

Here `s(γ₁ − γ₂)` is an `F[γ₁]`-linear endomorphism of `V`. Restriction of
scalars places it in the ambient algebra `End_F(V)`. The published
`subfieldEmbedding` places `δ` there too, and `𝔓^{1−r}` is
`S.chain.endFiltration (1 − S.r)`.

This is exactly the second conjunct of the published
`StratumApproximationStatement` (T7), stated on its own. The field witness
`h` does not add a hypothesis: `F[γ₁]` is a field because `S` is simple,
and the statement is required for every witness. Parts (ii)(a),(b) of the
source are in `StratumEquivalenceStatement` (T5) and are not repeated.

The source's common hereditary order is represented by one fixed
lattice-chain presentation, via `T.chain = S.chain`.
