# Labels of simple strata by induction on the level

This module proves BK94 (1.14) for principal orders,
Bushnell–Kutzko 1994, `bushnell-kutzko-1994-simple-types-conjugacy-classes`,
printed pp. 116–117, from two inputs stated elsewhere in the Library:
`PureStratumSimpleApproximationStatement` (BK93 (2.4.1)(i)) and
`MinimalSimpleStratumPolynomialStatement` (BK94 (1.4)–(1.5)).

## Definitions

- `LabelStrata L n m`: the simple strata `[𝔄,n,m,β]` on the chain `L`.
- `LabelValues L n m`: the label set
  `P^m_n(e(𝔄), N/e(𝔄); q_F)` as a subtype.
- `IsStratumLabelling L n m ρ`: equal labels imply `𝔄^×`-conjugacy up to
  equivalence, and `d(ρ(β)) = f(F[β]|F)`,
  `e(F[β]|F) e(ρ(β)) = e(𝔄)` — the two clauses of
  `SimpleStratumLabelStatement`.

## Results

- `exists_isStratumLabelling_base` (`m = n − 1`): the label of a simple
  stratum is the single quadruple `(φ, n, deg φ, gcd(n, e(𝔄)))`, where
  `φ` is the image in `𝔽_q[X]` of the irreducible factor of its
  fundamental polynomial. The polynomial statement gives the conditions of
  (1.13)(ii), the invariants (1.5), and conjugacy for equal factors;
  `N/e(𝔄) > 0` by `PureApproximation.period_le_finrank`.
- `exists_isStratumLabelling_step` (`0 ≤ m`, `m + 1 < n`): from a
  labelling `ρ'` at level `m + 1` to one at level `m`. For each simple
  stratum `S` at level `m`, `PureStratumSimpleApproximationStatement`
  gives a simple stratum `T₀` at level `m + 1` equivalent to
  `[𝔄,n,m+1,β]` (the restriction map (1.6)). A representative `G` of the
  label `ρ'(T₀)` is chosen once for each label; the labelling property of
  `ρ'` gives `u ∈ 𝔄^×` with `u⁻¹T₀u` equivalent to `G`, and the conjugate
  `u⁻¹βu` lies in the fibre of `G` (`InFibre`). The label of `S` is
  `ρ'(G)` if the fibre labeller of `G` (`exists_isFibreLabeller`) gives
  `none`, and `ρ'(G)` followed by the new quadruple otherwise
  (`snoc_mem_labelSet`). Equal labels determine the same `ρ'(G)`, hence
  the same representative, and the same fibre value (`Label.snoc_injective`,
  `snoc_ne_of_mem_labelSet`); the fibre property then gives conjugacy.
  The invariants follow from those of `G` and conjugation invariance.
- `exists_isStratumLabelling`: induction on `n − m`.
- `Langlands.BushnellKutzko.simpleStratumLabel_of`: if
  `PureStratumSimpleApproximationStatement` holds at the universes of
  `F` and `V`, and `MinimalSimpleStratumPolynomialStatement` holds at those
  universes and for fields in the universe of `V` (the generated fields
  `F[γ] ⊆ End_F(V)`), then `SimpleStratumLabelStatement` holds.

The source proves a bijection; only the injectivity up to conjugacy and
the invariant formulas are proved here, as the statement asks. The
source's intertwining comparison (1.9) and the conjugacy theorem (1.3)
are not used: equal labels give conjugacy directly
(`exists_unit_conj_of_derived`).
