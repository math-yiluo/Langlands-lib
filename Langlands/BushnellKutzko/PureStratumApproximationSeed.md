# A first nonmaximal approximation (BK93 (2.4.3))

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, (2.4.3) and the paragraph before it, printed pp. 66–67 (PDF pp. 78–79). The proof uses (2.3.11), printed p. 60 (PDF p. 72), and (2.3.4), printed p. 58 (PDF p. 70).

## Premises

The seed theorem takes (2.3.11) and (2.3.4) as named premises. `PureApproximation.nonsplitRefinement` proves (2.3.4). [Nonsplit refinement](NonsplitRefinementProof.md)

Both premises are closed propositions over every nonarchimedean local field `F` and finite-dimensional `F`-space `V`, using the Library's `Stratum.IsPure`, `Stratum.IsNonsplit` and `Stratum.IsSimple`.

- `TopNonsplitPremise` ((2.3.11)): for every pure stratum `[𝓛,n,r,β]`, the stratum `[𝓛,n,n−1,β]` is nonsplit fundamental.
- `NonsplitRefinementPremise` ((2.3.4)): for every nonsplit fundamental stratum `S` there is a simple stratum `T` with `T.r = T.n − 1`, `S.coset ⊆ T.coset`, `S.n · e(T) = T.n · e(S)`, and every lattice of `S.chain` occurring as a lattice of `T.chain`.

## Statement

`CandidateSeedStatement` says the following, assuming both premises. Let `S = [𝓛,n,r,β]` be pure, at its critical level `k₀(β,𝓛) = −r`, with `[F[β]:F] = dim_F V`. Then some simple stratum `T` has `β ∈ T.coset` and `[F[T.b]:F] < [F[β]:F]`. This is (2.4.3) in the setting where the source applies it, after its reductions to the critical level and to a maximal generated field. The source's congruence `β ≡ γ₀ (mod 𝔓₀^{−r₀})` is the coset membership.

## Implemented proof

Apply (2.3.11) and then (2.3.4) to the top stratum `[𝓛,n,n−1,β]`. This gives a simple top stratum `T` whose coset contains that of the top stratum, hence contains `β`. A generated field acting on `V` has degree at most `dim V` (`elementDegree_le_finrank`). It remains to exclude equality. Suppose `[F[T.b]:F] = dim V`.

- `β ∈ T.coset` makes `[T.chain, T.n, T.r, β]` a stratum equivalent to `T`. Its valuation bound comes from `le_valuation_of_mem`. `maximalSimpleReflection` makes it simple.
- So `F[β]ˣ` normalizes both `𝓛` and `T.chain`, and `V` is a line over `F[β]` (`exists_line_generator`). `lineChainTranslation` makes the two chains translates of each other.
- Translates have equal periods, so the slope relation from (2.3.4) gives `T.n = n`.
- `chainTranslation` transports simplicity back to `[𝓛,n,n−1,β]`. Then `−r = k₀(β,𝓛) < 1 − n`, contradicting `r < n`.

The lattice-containment clause of (2.3.4) is not used. Neither the aggregate T7 nor any derived-stratum assertion is used.
