# Lemma II.4.1: the measure of the level sets `Ū(n)`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.LevelSetBound`, namespace
`Langlands.HarishChandraSchwartz`. It imports the published module `SphericalBounds`,
whose Prop-valued definitions `LevelSetMeasureBound` (the conclusion of Lemma II.4.1) and
`XiUpperBound` (the upper bound of Lemma II.1.1) are used here.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

II.4 and Lemma II.4.1 (printed pp. 259–261, PDF pp. 25–27). For `P = M U` standard and
`n ≥ 1`, `Ū(n) = {ū ∈ Ū ; δ_0(m_0(ū)) = q^{-n}}`, and Lemma II.4.1 states that there are
`c > 0` and `d ∈ ℕ` with `mes(Ū(n)) ≤ c q^{n/2} n^d` for all `n ≥ 1`. With
`γ(a) = sup{|α(a)|_F ; α ∈ Δ(P)}` for `a ∈ A_M`, the proof shows:

- (1): there are `C_1 > 0` and `r > 0` with
  `δ_0(m_0(a^{-1} ū a))^{-1/2} ≤ C_1 [1 + γ(a)^r δ_0(m_0(ū))^{-1/2}]` for `ū ∈ Ū` and
  `a ∈ A_M ∩ Ā⁺_0` (from the representation `τ_0` of II.2);
- (2): `Ξ(a) = γ(G|M)^{-1} δ_0(a)^{1/2} ∫_Ū δ_0(m_0(a^{-1} ū a) m_0(ū))^{1/2} dū` for
  `a ∈ A_M` (from `Ξ(a) = ∫_{P_0\G} e(g a) e(g) dg` and the integration formulas of I.1);
- (3): by (1), (2) and Lemma II.1.1, there are `C_3 > 0`, `r > 0`, `d ∈ ℕ` with
  `∫_Ū [1 + γ(a)^r δ_0(m_0(ū))^{-1/2}]^{-1} δ_0(m_0(ū))^{1/2} dū ≤ C_3 (1 + σ(a))^d` for
  `a ∈ A_M ∩ Ā⁺_0`;
- then, for a fixed `a` with `γ(a) < 1` and `m` the least integer with
  `γ(a)^{r m} ≤ q^{-n/2}`, (3) at `a^m` restricted to `Ū(n)` gives
  `(1/2) q^{-n/2} mes(Ū(n)) ≤ C_3 (1 + σ(a^m))^d ≤ C_4 n^d`.

## Scope: abstract data and explicit hypotheses

The module works with a subgroup `U` (Waldspurger's `Ū`) of a group `G` with a measure `ν`,
a subgroup `M`, a set `T ⊆ M` (his `A_M ∩ Ā⁺_0`), functions `Ξ, σ, e : G → ℝ`,
`w : U → ℝ` (his `δ_0(m_0(ū))^{1/2}`), `g : M → ℝ` (his `γ`), a real `γ > 0` (his
`γ(G|M)`) and maps `c_a : U → U` for `a ∈ M` (his `ū ↦ a^{-1} ū a`). Formula (2),
inequality (1) and the upper bound of Lemma II.1.1 are hypotheses; so are the facts used
about the element `a` (`a^m ∈ T`, `g(a^m) = g(a)^m`, `σ(a^m) ≤ m σ(a)`, `0 < g(a) < 1`) and
the level structure `w = q^{-N/2}` with `N : U → ℤ` measurable and `q > 1`. None of them is
proved here for Waldspurger's data; in particular (1) and (2) are in-book deductions
(from II.2 and from I.1, II.1) that remain proof obligations.

## Definitions

- `TorusXiFormula ν Ξ T γ e w c : Prop`: for every `a ∈ T`,
  `Ξ(a) = γ^{-1} e(a) ∫_U w(c_a(u)) w(u) dν(u)`, written with `ENNReal.ofReal` and a lower
  integral. With Waldspurger's data and `δ_0(m_0(a^{-1} ū a) m_0(ū)) = δ_0(m_0(a^{-1} ū a))
  δ_0(m_0(ū))` this is formula (2).

## Results

- `levelSetMeasureBound_of_powers` (second step): for a measurable space `X`, a measure
  `ν`, measurable `N : X → ℤ`, `w = q^{-N/2}` with `q > 1`, and reals `0 < θ < 1`, `r > 0`,
  `s ≥ 0`, `d ≥ 0`, `C_3`: if
  `∫⁻ (1 + θ^{r m} w(x)^{-1})^{-1} w(x) dν(x) ≤ C_3 (1 + m s)^d` for every `m ∈ ℕ`, then
  there are `C` and `d'` with `ν{N = n} ≤ C q^{n/2} n^{d'}` for every `n ≥ 1`.
- `averages_le_of_torusXiFormula` (inequality (3)): assume `TorusXiFormula ν Ξ T γ e w c`,
  `γ > 0`, `e > 0` on `T`, `w > 0`, `g ≥ 0` on `T`, inequality (1)
  `w(c_a(u))^{-1} ≤ C_1 (1 + g(a)^r w(u)^{-1})` for `a ∈ T`, and
  `XiUpperBound Ξ σ T e` (on the image of `T` in `G`). Then there are `C_3`, `d` with
  `∫⁻ (1 + g(a)^r w(u)^{-1})^{-1} w(u) dν(u) ≤ C_3 (1 + σ(a))^d` for `a ∈ T`.
- `levelSetMeasureBound_of_torusXiFormula` (Lemma II.4.1): under the hypotheses of the
  previous result with `w = q^{-N/2}` (`q > 1`, `N` measurable), `σ ≥ 0`, `r > 0`, and an
  element `a ∈ M` with `a^m ∈ T`, `g(a^m) = g(a)^m` and `σ(a^m) ≤ m σ(a)` for all
  `m ∈ ℕ` and `0 < g(a) < 1`, `LevelSetMeasureBound ν N q` holds.

## Proof notes

- (3). From (1), `(1 + g(a)^r w(u)^{-1})^{-1} ≤ C_1' w(c_a(u))` with `C_1' = max(C_1, 1)`;
  so the integral is at most `C_1' ∫ w(c_a(u)) w(u) dν = C_1' γ e(a)^{-1} Ξ(a)` by (2), and
  `Ξ(a) ≤ C e(a) (1 + σ(a))^d` gives `C_3 = C_1' γ C`.
- Second step. With `L = log q / (2 r (−log θ))`, take `m = ⌈n L⌉`, so that
  `θ^{r m} ≤ q^{-n/2}` (not necessarily the least such integer, which Waldspurger uses).
  On `{N = n}`, `w = q^{-n/2}`, hence `θ^{r m} w^{-1} ≤ 1` and the integrand is at least
  `(1/2) q^{-n/2}`. This gives `ν{N = n} ≤ 2 q^{n/2} C_3 (1 + m s)^d`, and
  `m ≤ n L + 1 ≤ (L + 1) n` gives `(1 + m s)^d ≤ (1 + (L + 1) s)^d n^d`.
- Lemma II.4.1. Apply (3) at `a^m`, using `g(a^m)^r = g(a)^{r m}` and
  `1 + σ(a^m) ≤ 1 + m σ(a)`, after replacing `C_3` by `max(C_3, 0)` and `d` by
  `max(d, 0)`.

## Open obligations

For Waldspurger's data: inequality (1), formula (2) (which needs the identification of
`Ξ` with the matrix coefficient `∫_{P_0\G} e(g a) e(g) dg` and the integration formulas of
I.1), the upper bound of Lemma II.1.1, the existence of `a ∈ A_M ∩ Ā⁺_0` with `γ(a) < 1`
and the properties of its powers, and the identity `δ_0(m_0(ū)) = q^{-N(ū)}` with `N`
measurable are not proved here.
