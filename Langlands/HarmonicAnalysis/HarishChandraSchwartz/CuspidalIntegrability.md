# Corollary VIII.3.2: integrability modulo `A_G`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalIntegrability`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published module
`CuspidalDecay`, whose Prop `ConjugationIntegralBound` is the conclusion of Proposition
VIII.3.1.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Corollary VIII.3.2 and its proof, printed pp. 326–327 (PDF
pp. 92–93): for `f_1 ∈ °C(G)` and `f_2 ∈ C(G)`,
`∫_{A_G\G} |∫_G f_1(h g h^{-1}) f_2(g) dg| dh` converges. Proof: there is a compact
`Γ ⊂ M_0` such that `⋃_{a ∈ (Ā⁺_0 ∩ G^1)/(Ā⁺_0 ∩ M_0^1)} K a Γ K` projects onto `A_G\G`;
"using the smoothness of `f_1` and `f_2`", Proposition VIII.3.1 gives
`∫_{KaΓK} |∫_G f_1(h g h^{-1}) f_2(g) dg| dh ≤ C_1 mes(KaΓK) δ_0(a) (1 + σ(a))^{-r}`; by
I.1 (5), `mes(KaΓK) ≤ C_2 δ_0(a)^{-1}`; and for `r` large the series
`∑_a (1 + σ(a))^{-r}` converges.

## Scope: abstract data and explicit hypotheses

`G` is a group with a measurable multiplication and a measure `μ` that is both left and
right invariant (Waldspurger's unimodular `G` with its Haar measure; no Haar property is
assumed); `M` is a subgroup, `T ⊆ M` (his `Ā⁺_0 ∩ G^1`), `e : M → ℝ` (his `δ_0^{1/2}`) and
`σ : G → ℝ`. `X` is a measurable space with a measure `μ_X` and a map `π : G → X` (his
`A_G\G` with its quotient measure; no quotient structure is assumed), and `ι` is a
countable index set (his `(Ā⁺_0 ∩ G^1)/(Ā⁺_0 ∩ M_0^1)`). `f_1, f_2 : G → ℂ` are arbitrary;
`f^y(g) = f(y g y^{-1})` denotes a conjugate. The explicit hypotheses of the main theorem
`lintegral_lt_top_of_conjugationIntegralBound` are, none of them proved here for
Waldspurger's data:

- `he`: `e(a) > 0` for `a ∈ T`; `hσ`: `σ(g) ≥ 0` for all `g`;
- `hF`: `F : X → ℝ≥0∞` satisfies `F(π(h)) = |∫ f_1(h g h^{-1}) f_2(g) dμ(g)|` for all `h`
  (for Waldspurger, the `A_G`-invariance of the inner integral, which lets it descend);
- `hcover`: sets `Ω(i) ⊆ X` cover `X`;
- `haT`: representatives `a_i ∈ T`;
- `hcell`: sets `K', Y ⊆ G` such that every point of `Ω(i)` is `π(k a_i y)` with `k ∈ K'`,
  `y ∈ Y` (for Waldspurger: `K' = K`, `Y = Γ K`, `Ω(i)` the image of `K a_i Γ K`);
- `hfin₁`, `hfin₂`: the sets `{f_1^k : k ∈ K'}` and `{f_2^{y^{-1}} : y ∈ Y}` are finite (for
  Waldspurger this is where the smoothness of `f_1` and `f_2` and the compactness of `K`
  and `Γ K` enter);
- `h31`: Proposition VIII.3.1 for each of these pairs,
  `ConjugationIntegralBound μ T (f_1^k) (f_2^{y^{-1}}) e σ` for `k ∈ K'`, `y ∈ Y`, that is,
  for every `r` a constant `c` with `|∫ f_1^k(a g a^{-1}) f_2^{y^{-1}}(g) dμ| ≤
  c e(a)^2 (1 + σ(a))^{-r}` on `T`;
- `hm`: the measure bound `μ_X(Ω(i)) ≤ C_2 e(a_i)^{-2}` (the form of Waldspurger's I.1 (5),
  `mes(K a Γ K) ≤ C_2 δ_0(a)^{-1}`, needed on the quotient);
- `hsum`: summability of `(1 + σ(a_i))^{-r}` for one real `r`.

## Definitions

- `conjFun y f = (g ↦ f(y g y^{-1}))`, the conjugate `f^y`.

## Results

- `lintegral_le_tsum_of_cover`: on any measure space, for a countable family `Ω` covering
  the space (`hcover`), `F ≤ s(i)` on `Ω(i)` (`hs`) and `μ(Ω(i)) ≤ m(i)` (`hm`) give
  `∫⁻ F ≤ ∑_i s(i) m(i)`. No measurability of `F` or of the `Ω(i)` is assumed.
- `lintegral_lt_top_of_cells`: for a countable cover (`hcover`), `e(i) > 0` (`he`),
  `t(i) ≥ 0` (`ht`), `F ≤ C_1 e(i)^2 (1 + t(i))^{-r}` on `Ω(i)` (`hs`),
  `μ(Ω(i)) ≤ C_2 e(i)^{-2}` (`hm`) and summability of `(1 + t(i))^{-r}` (`hsum`), with
  arbitrary real `C_1`, `C_2`, `r`: `∫⁻ F < ∞`.
- `integral_conj_mul_conj`: for `μ` left and right invariant, any `f_1, f_2` and
  `k, a, x ∈ G`,
  `∫ f_1((k a x) g (k a x)^{-1}) f_2(g) dμ = ∫ f_1^k(a g a^{-1}) f_2^{x^{-1}}(g) dμ`.
- `ConjugationIntegralBound.uniform`: for a finite set `S` of pairs (`hS`) each satisfying
  `ConjugationIntegralBound μ T p.1 p.2 e σ` (`h`), and each real `r`, one constant `c`
  gives the bound of Proposition VIII.3.1 for all pairs of `S` and all `a ∈ T`.
- `lintegral_lt_top_of_conjugationIntegralBound` (Corollary VIII.3.2): under the hypotheses
  listed in the scope, `∫⁻ F dμ_X < ∞`.

## Proof notes

The proof is Waldspurger's, with the smoothness step made explicit. On `Ω(i)`, write
`x = π(k a_i y)`; then `F(x) = |∫ f_1^k(a_i g a_i^{-1}) f_2^{y^{-1}}(g) dμ|` by the change
of variables `g ↦ y^{-1} g y` (`integral_conj_mul_conj`), and the uniform constant for the
finitely many pairs gives `F ≤ c e(a_i)^2 (1 + σ(a_i))^{-r}` on `Ω(i)`. Waldspurger bounds
the integral over the cell by its measure times this bound; here the same is done by
`lintegral_le_tsum_of_cover` (lower integral over the union bounded by the sum over the
cells, no measurability of the cells being needed), and the factors `e(a_i)^2` and
`e(a_i)^{-2}` cancel.

## Open obligations

For Waldspurger's data: the existence and properties of `A_G\G` with its quotient measure
and of the descended integrand; the cover by the cells `K a Γ K`; the finiteness of the
conjugates from smoothness; Proposition VIII.3.1 itself (proved in `CuspidalDecay` from
explicit hypotheses); the measure bound I.1 (5) on the quotient; and the summability over
the lattice (from I.1 (6) and the discreteness of `H_0(A_0)`) are not proved here.
