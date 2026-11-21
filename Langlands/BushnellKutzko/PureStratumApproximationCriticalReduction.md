# Pure-stratum approximation: reduction to the critical level

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`. See (2.4.1)(i), printed p. 65 (PDF p. 77), the opening of its proof, printed p. 66 (PDF p. 78), and the computation before (2.4.7) and the numbered assertion itself, printed p. 71 (PDF p. 83).

`CriticalPureStratumSimpleApproximationStatement` restricts the published witness form of (2.4.1)(i), `PureStratumSimpleApproximationStatement`, to pure strata `[𝓛,n,r,β]` with `k₀(β,𝓛) = −r`. Its witness is simple on the same chain and at the same integers, is equivalent to the input, and has ramification index and residue degree dividing those of the input's field, respectively. The computation on p. 71 before (2.4.7) gives the two divisibilities. The numbered assertion (2.4.7) gives critical-level existence and equivalence and includes a further derived-stratum conclusion, which is not required here.

`PureStratumApproximationCriticalReductionStatement` is the implication from that restricted assertion to the published assertion. It isolates the preliminary induction in the opening proof of (2.4.1)(i) on p. 66; it does not assert that the critical-level witness exists. The numbered assertion (2.4.3) on p. 67 instead gives an auxiliary simple approximation with nonmaximal field, after the preliminary reductions.

## Implemented proof

`pureStratumApproximationCriticalReduction` uses strong induction on `(n + k₀).toNat` when `k₀` is an integer, using measure zero for `k₀ = −∞`. A simple input is its own witness. Otherwise `k₀` is an integer `k ≥ −r`. The pure stratum with depth changed to `−k` is well-defined since `−k ≤ r < n`. Apply the restricted assertion to get `γ`, simple at depth `−k`, with the two desired divisibilities and `β − γ ∈ 𝔓^k`.

Put `γ` at the original depth `r`. It remains pure, and `𝔓^k ⊆ 𝔓^{−r}` gives equivalence by `Stratum.equivalent_of_sub_mem`. If this stratum is simple, return it. Otherwise its critical exponent is an integer `j`; simplicity at depth `−k` gives `j < k`, and `neg_n_le_criticalExponent minimalCriticalExponent` gives `−n ≤ j`. The induction measure strictly decreases. Apply the induction hypothesis, then compose the equivalences and the two divisibilities separately. No nonnegativity hypothesis on `n` or `r` is added. Neither the aggregate approximation theorem nor any assertion on derived strata is used as a premise.
