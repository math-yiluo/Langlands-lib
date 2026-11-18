# Proof of the equal-rank unfolding

Module `Langlands.Global.RankinSelberg.EqualUnfoldingProof`, namespace
`Langlands.Global.RankinSelbergGlobal`.

`equalUnfoldingStatement_proof` proves the Library statement
`Langlands.Global.RankinSelbergGlobal.EqualUnfoldingStatement.{u}` unchanged. That statement
is the ordinary and dual unfolding of the equal-rank global Rankin–Selberg integral into the
global Whittaker integral: J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
§2.3, printed p.210 for `I(s; φ, φ', Φ) = Ψ(s; W_φ, W'_φ', Φ)` and the remark after
Theorem 2.2 on printed p.211 for `I(1 - s; φ̃, φ̃', Φ̂) = Ψ(1 - s; W̃_φ, W̃'_φ', Φ̂)` (source
`cogdell-2004-analytic-theory-gln`). It covers every number field `F : Type u` with
`CompactSpace (AdeleQuotient F)`, every `r` and every pair of actual cuspidal realizations
`T`, `T'` of `GL_(r+1)` with central characters `ω`, `ω'`. The half-plane bound `C ≥ 0`
depends only on `T`, `T'`, `ω`, `ω'` and is uniform over standard additive characters `ψ`,
vectors and Schwartz–Bruhat functions. The universe `u` and every hypothesis are kept.

## Declarations

```
theorem equalUnfoldingStatement_of_gauge (hG : EqualUnfoldingGaugeStatement.{u}) :
    EqualUnfoldingStatement.{u}

theorem equalUnfoldingStatement_proof : EqualUnfoldingStatement.{u}
```

`equalUnfoldingStatement_of_gauge` says: if the gauge integrability premises G and G̃
(`EqualWhittakerGaugeIntegrable F T T'` and `DualEqualWhittakerGaugeIntegrable F T T'`,
module `EqualUnfoldingReduction`) hold for every number field `F` with compact `𝔸_F/F`, every
`r` and every pair `T`, `T'`, then `EqualUnfoldingStatement` holds. The statement
`EqualUnfoldingGaugeStatement` (module `EqualUnfoldingGaugeStatement`) is exactly the
conjunction of G and G̃ over all such pairs.

## Implemented proof

The proof is a composition of published results. It adds no new mathematics.

1. `equalUnfoldingReduction : EqualUnfoldingReductionStatement` (module
   `EqualUnfoldingReduction`) proves `EqualUnfoldingStatement` from the premises
   `EqualUnfoldingPremises F T T'` for all pairs. These are four premises, in this order:
   - E, `CuspidalWhittakerExpansion F T`: the Library theorem
     `cuspidalWhittakerExpansionStatement_proof F r T` (module
     `CuspidalWhittakerExpansionProof`);
   - Ẽ, `DualCuspidalWhittakerExpansion F T`: the Library theorem
     `dualCuspidalWhittakerExpansionStatement_proof F r T` (module
     `DualWhittakerExpansionProof`);
   - G and G̃: the two components `hG.1 F r T T'` and `hG.2 F r T T'` of the gauge
     hypothesis.

   This gives `equalUnfoldingStatement_of_gauge`.
2. `equalUnfoldingGauge : EqualUnfoldingGaugeStatement` (module `EqualUnfoldingGauge`)
   proves the gauge hypothesis. It applies `equalGaugeAnalyticReduction` to the analytic gauge
   bound `whittakerSchwartzGauge`.

`equalUnfoldingStatement_proof` is `equalUnfoldingStatement_of_gauge equalUnfoldingGauge`.
The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the source

Cogdell replaces the Eisenstein series by its definition and unfolds to an integral over
`P_n(F) \ GL_n(𝔸)`. He then replaces `φ` by its Fourier (Whittaker) expansion and unfolds
again to `Ψ(s; W_φ, W'_φ', Φ)` over `N_n(𝔸) \ GL_n(𝔸)`, which "converges for `Re(s) ≫ 0`".
He unfolds the right-hand side of the functional equation in the same way, with convergence
for `Re(s) ≪ 0`. The Library proof follows this route. `equalUnfoldingReduction` carries out
both unfoldings. The premises E and Ẽ are the Whittaker expansions of the cusp form and of its
dual. The premises G and G̃ give the absolute convergence that justifies exchanging sums and
integrals in the two half-planes.
