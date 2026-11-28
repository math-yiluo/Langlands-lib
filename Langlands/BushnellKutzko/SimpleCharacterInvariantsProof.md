# Invariants from a common simple character: proof

The module proves `Langlands.BushnellKutzko.SimpleCharacterInvariantsStatement` as the theorem
`Langlands.BushnellKutzko.simpleCharacterInvariants`, with no additional hypotheses
(Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(3.5.1), printed p. 117). The lemmas in the namespace `CentralizerResidue` cited below are in
the module `IntertwiningCentralizerComparison`, except `simpleHGroup_eq_inf_unitFiltration`
and `not_simpleCriticalDepth_lt`, which are proved here.

**Statement.** Let `F` be a nonarchimedean local field, `V` a finite-dimensional `F`-space,
`ψ_F` an additive character with the BK93 conductor convention, `L` a lattice chain with
order `𝔄`, and `0 ≤ m < n`. If two simple strata `[𝔄,n,m,β]` and `[𝔄,n,m,β']` on `L` share
a pair `(H, θ)` (a group `H^{m+1}` with a character `θ ∈ C(𝔄,m,β) ∩ C(𝔄,m,β')`), then
`k₀(β,𝔄) = k₀(β',𝔄)`, `e(F[β]|F) = e(F[β']|F)` and `f(F[β]|F) = f(F[β']|F)`.

**Proof as implemented.**

1. *Reduction to level zero.* A simple stratum `[𝔄,n,m,β]` with `m ≥ 0` gives a simple
   stratum `[𝔄,n,0,β]` (`Stratum.isSimple_atDepthZero`). A defining sequence for the former
   gives one for the latter with the same tail (`DefiningSequenceChoice.atDepthZero`), so
   `θ` is literally a simple character of the level-zero stratum. The index `m` lies below
   `n` and below both critical depths (`CentralizerResidue.lt_simpleCriticalDepth_of_isSimple`).
2. *`𝔅 + 𝔓`, `e` and `f`.* By (3.3.2) (`simpleCharacterIntertwining`), the self-intertwining
   of the common character is `Y B_β^× Y = Y' B_{β'}^× Y'`.
   `CentralizerResidue.sup_eq_of_pair_eq` turns this into `𝔅_β + 𝔓 = 𝔅_{β'} + 𝔓`, and
   `CentralizerResidue.invariants_eq_of_sup_eq` gives the equalities of `e` and `f`.
3. *The critical exponents.* `CentralizerResidue.not_simpleCriticalDepth_lt` shows that the
   critical depth `r = −k₀(β,𝔄)` is not smaller than `r' = −k₀(β',𝔄)`, and by symmetry the
   two depths are equal. `CentralizerResidue.criticalExponent_eq_of_simpleCriticalDepth_eq`
   then gives `k₀(β,𝔄) = k₀(β',𝔄)`. Suppose `r < r'`.
   - If `β` is scalar, `r = ∞`, which is impossible. If `β'` is scalar,
     `𝔅_β + 𝔓 = 𝔅_{β'} + 𝔓 = 𝔄`, forcing `β` scalar
     (`CentralizerResidue.elementAlgebra_eq_bot_of_sup_eq_top`).
   - If the defining sequence of `β` has length one, then `r = n ≥ r'`
     (`level_eq_of_terminal_of_criticalExponent_eq`, `criticalDepth_of_simple`).
   - Otherwise `exists_simpleCharacterSuffix` gives the next term: a simple stratum
     `[𝔄,n,0,γ]` with `β − γ ∈ 𝔓^{−r}`, `k₀(γ,𝔄) < −r`, a defining sequence for `γ` whose
     tail continues that of `β`, and `H^{r+1}(β) = H^{r+1}(γ)`. By
     `CentralizerResidue.exists_pair_eq_at_jump` and the forward restriction
     `simpleCharacters_restrict_forward` for `γ`, the restriction of `θ` to `H^{r+1}(β)`
     is a simple character of `[𝔄,n,r,γ]`. The forward restriction for `β'` (valid since
     `r < r'`) shows that the restriction of `θ` to `H^{r+1}(β')` is a simple character of
     `[𝔄,n,r,β']`. The two groups agree, since `H^{r+1} = H^{m+1} ∩ U^{r+1}(𝔄)` for both
     strata (`CentralizerResidue.simpleHGroup_eq_inf_unitFiltration`, from the subgroup
     properties (3.1.14)). So the restrictions are one pair, and step 2 at index `r` gives
     `𝔅_γ + 𝔓 = 𝔅_{β'} + 𝔓 = 𝔅_β + 𝔓`. This contradicts
     `CentralizerResidue.sup_ne_of_criticalExponent_eq`:
     `𝔑_{−r}(β) = 𝔑_{−r}(γ) ⊆ 𝔅_γ + 𝔓` would leave `−r` outside the critical index set of
     `β`, while `k₀(β,𝔄) = −r`.

**Relation to the source.** Steps 1 and 2 follow the first paragraph of the proof of (3.5.1).
For the equality of the critical exponents BK93 also restricts the common character to the
first jump, but derives a contradiction from `[F[γ]:F] = [F[β']:F] = [F[β]:F]` using (2.4.1)
and (2.2.8). The Lean proof stops at the equality of `𝔅 + 𝔓`, which already contradicts the
definition (1.4.5) of `k₀`.

## Source

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (3.5.1), printed p. 117 (PDF p. 129); (3.3.2), printed p. 105; (3.1.14), printed
p. 95; (1.4.5), printed p. 36. Literature ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
