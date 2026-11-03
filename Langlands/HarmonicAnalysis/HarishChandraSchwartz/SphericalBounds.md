# Bounds for `Ξ` and for the weight on `Ū` (Lemmas II.1.1, II.4.2, II.4.4)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalBounds`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound`, whose Prop-valued
definitions `XiLowerBound`, `UnipotentXiBound`, `UnipotentWeightIntegrable` and
`IsDoubleCosetCover` are the conclusions and hypotheses here, and `Mathlib.Analysis.PSeries`
(convergence of `∑ n^p` for `p < -1`). Through `ConstantTermBound` it uses
`IsIwasawaPair`, `iwasawaWeight`, `normalizedHaar` and `xi` of the published module
`Spherical`, with the lemmas `iwasawaWeight_mul`, `iwasawaWeight_mul_left`,
`iwasawaWeight_mul_right`, `iwasawaWeight_nonneg` and `integrable_iwasawaWeight_mul`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- II.1 (printed pp. 250–251, PDF pp. 16–17): `Ξ(g) = ∫_K δ_0(m_0(kg))^{1/2} dk`.
- Lemma II.1.1 (printed p. 251, PDF p. 17): `Ξ` is bi-invariant under `K`, and there are
  `C_1, C_2 > 0` and `d ∈ ℕ` with `C_1 δ_0(m)^{1/2} ≤ Ξ(m) ≤ C_2 δ_0(m)^{1/2} (1 + σ(m))^d`
  for `m ∈ M̄⁺_0`. Proof of the lower bound: let `H` be a compact open subgroup of `K`
  with `H = (H ∩ U_0)(H ∩ M_0)(H ∩ Ū_0)`. For `m ∈ M̄⁺_0`, `m^{-1}(H ∩ Ū_0) m ⊂ K`, so
  `H m ⊂ U_0 m K` and `δ_0(m_0(hm)) = δ_0(m)` for `h ∈ H`; hence
  `Ξ(m) ≥ ∫_H δ_0(m_0(hm))^{1/2} dh = mes(H) δ_0(m)^{1/2}`. The upper bound uses
  Proposition I.4.3 (Casselman).
- Lemma II.3.2 (printed p. 255, PDF p. 21): there is `C > 0` with
  `δ_0(m) ≤ C δ_0(m_0(g))` for `m ∈ M̄⁺_0` and `g ∈ K m K`.
- Lemma II.3.4 (printed pp. 256–257, PDF pp. 22–23): for a semi-standard `P = M U` there
  are `C_0, C_1, C_2, C_3 > 0` with
  `C_1 (1 + σ(ū)) ≤ C_0 - log δ_P(m_P(ū)) ≤ C_2 (1 + σ(m_P(ū))) ≤ C_2 (1 + σ(ū))` for
  `ū ∈ Ū`.
- II.4 (printed p. 259, PDF p. 25): for `P = M U` standard and `n ≥ 1`,
  `Ū(n) = {ū ∈ Ū ; δ_0(m_0(ū)) = q^{-n}}`. Lemma II.4.1: there are `c > 0` and `d ∈ ℕ`
  with `mes(Ū(n)) ≤ c q^{n/2} n^d` for all `n ≥ 1`.
- Lemma II.4.2 (printed p. 261, PDF p. 27): for some `d ∈ ℕ` the integral
  `∫_Ū δ_0(m_0(ū))^{1/2} (1 + σ(ū))^{-d} dū` converges. Proof: by Lemma II.3.4, `Ū` is
  the union of a compact set and the `Ū(n)`, `n ≥ 1`; on `Ū(n)` the integral is at most
  `c n^{d'-d}` ("ce lemme et le Lemme II.3.3", where `d'` is the exponent of II.4.1);
  `d ≥ d' + 2` suffices.
- Lemma II.4.4 (printed p. 262, PDF p. 28): there are `d ∈ ℕ` and `c > 0` with
  `Ξ(m ū) ≤ c δ_0(m)^{1/2} δ_0(m_0(ū))^{1/2} (1 + σ(m ū))^d` for `m ∈ M_0`, `ū ∈ Ū`.
  Proof: write `m ū ∈ K h K` with `h ∈ M̄⁺_0` (I.1 (4)); then `Ξ(m ū) = Ξ(h)`,
  `σ(h) = σ(m ū)`, the upper bound of Lemma II.1.1 at `h`, and Lemma II.3.2:
  `δ_0(h) ≤ C δ_0(m_0(m ū)) = C δ_0(m) δ_0(m_0(ū))`.

## Scope: abstract data and explicit hypotheses

The reductive group, `P_0 = M_0 U_0`, `K`, the Cartan decomposition, the Iwahori
factorization, the Haar measure on `Ū` and the modulus characters are not constructed.
`Ξ` is either the function `xi hPK δ` of `Spherical`, defined by the integral formula of
II.1 from data `G = P K` (`hPK : IsIwasawaPair P K`, `K` compact open) and a character
`δ : P →* ℝ≥0ˣ` trivial on `P ∩ K`, or an arbitrary function `Ξ : G → ℝ`. The weight
`φ = iwasawaWeight hPK δ` is `φ(p k) = δ(p)^{1/2}`; for Waldspurger's `P = P_0` and
`δ = δ_0 ∘ m_0` it is `g ↦ δ_0(m_0(g))^{1/2}`. As stated in `Spherical`, the
identification of `xi` with the matrix coefficient `⟨π(g)e, e⟩` and the specialization to
Waldspurger's `P_0`, `K` and `δ_0` are not done.

## Lemma II.1.1, lower bound

- `iwasawaWeight_mul_of_mem`: for `g ∈ P` and `x ∈ G`, `φ(g x) = φ(g) φ(x)`.
- `iwasawaWeight_mul_mul_eq`: for `p ∈ P ∩ K` and `g⁻¹ v g ∈ K`, `φ(p v g) = φ(g)`.
- `measureReal_mul_iwasawaWeight_le_xi`: for an open set `H ⊆ G` and `g ∈ G` with
  `φ(h g) = φ(g)` for all `h ∈ H`, `μ_K(H ∩ K) φ(g) ≤ Ξ(g)`, where `μ_K` is the Haar
  measure of `K` of total mass one (`normalizedHaar K`).
- `xiLowerBound_of_factorization`: let `H ≤ K` be an open subgroup and `V`, `S` subsets
  of `G` such that every `h ∈ H` is `p v` with `p ∈ P ∩ H` and `v ∈ V`, and
  `g⁻¹ v g ∈ K` for `g ∈ S` and `v ∈ V`. Then `XiLowerBound (xi hPK δ) S φ`, with
  constant `μ_K(H)^{-1}`.

For Waldspurger's data, `H = (H ∩ U_0)(H ∩ M_0)(H ∩ Ū_0)` gives the factorization with
`p ∈ (H ∩ U_0)(H ∩ M_0) ⊆ P_0 ∩ H` and `V = H ∩ Ū_0`; the inclusions
`m^{-1}(H ∩ Ū_0) m ⊂ K` for `m ∈ S = M̄⁺_0` are the second input; and `φ(m) = δ_0(m)^{1/2}`
for `m ∈ M_0`. The existence of such an `H` and these inclusions are not proved here
(structural ledger row WSH-IWAHORI-01). The Lean statement does not need `S ⊆ P`.

## Lemma II.4.4

- `XiUpperBound Ξ σ S e : Prop` (for functions on any type `X`): there are real `C` and
  `d` with `Ξ(x) ≤ C e(x) (1 + σ(x))^d` for `x ∈ S`. With `S = M̄⁺_0` and `e = δ_0^{1/2}`
  this is the upper bound of Lemma II.1.1; with `S = G` and `e = φ` it is the global
  bound proved below.
- `CartanWeightComparison K S φ : Prop`: there is `C` with `φ(s) ≤ C φ(k₁ s k₂)` for
  `s ∈ S` and `k₁, k₂ ∈ K`. For `S = M̄⁺_0` and `φ = δ_0(m_0(·))^{1/2}` (so that
  `φ(m) = δ_0(m)^{1/2}` on `M_0`) this is Lemma II.3.2, with the constant `C^{1/2}`.
- `XiUpperBound.univ_of_cartan`: if `IsDoubleCosetCover K S` (`G = K S K`, the covering
  part of I.1 (4)), `Ξ` and `σ` are bi-invariant under `K`, `σ ≥ 0`, `φ ≥ 0`,
  `XiUpperBound Ξ σ S φ` and `CartanWeightComparison K S φ`, then
  `XiUpperBound Ξ σ Set.univ φ`: `Ξ(g) ≤ C φ(g) (1 + σ(g))^d` for all `g ∈ G`.
- `XiUpperBound.unipotentXiBound`: from the global bound and `φ(m u) = e(m) w(u)` for
  `m ∈ S ⊆ M` and `u ∈ U`, `UnipotentXiBound Ξ σ S e w`.
- `XiUpperBound.unipotentXiBound_iwasawaWeight`: for `φ = iwasawaWeight hPK δ` and
  `S ⊆ M` contained in `P`, `UnipotentXiBound Ξ σ S (φ ∘ val) (φ ∘ val)`, using
  `iwasawaWeight_mul_of_mem`. For Waldspurger's `M_0 ⊆ P_0` this is Lemma II.4.4 with
  `e(m) = δ_0(m)^{1/2}` and `w(ū) = δ_0(m_0(ū))^{1/2}`.

The proof is Waldspurger's: for `g = k₁ s k₂`, `Ξ(g) = Ξ(s) ≤ C φ(s) (1 + σ(s))^d` and
`φ(s) ≤ C' φ(g)`, `σ(s) = σ(g)`. The constants `C`, `C'` are replaced by `max(C, 0)`,
`max(C', 0)`. The identity `δ_0(m_0(m ū)) = δ_0(m) δ_0(m_0(ū))` of the article is
`iwasawaWeight_mul_of_mem`.

## Lemma II.4.2

- `LevelSetMeasureBound ν N q : Prop`, for a measure `ν` on `U`, `N : U → ℤ` and real
  `q`: there are real `C` and `d` with `ν{u : N(u) = n} ≤ C q^{n/2} n^d` for every
  natural `n ≥ 1`. With `δ_0(m_0(ū)) = q^{-N(ū)}`, `{N = n}` is Waldspurger's `Ū(n)` and
  this is Lemma II.4.1.
- `LevelHeightComparison U N q σ : Prop`: there are `C₀`, `C₁ > 0` and `C₂ > 0` with
  `C₁ (1 + σ(u)) ≤ C₀ + N(u) log q ≤ C₂ (1 + σ(u))` for all `u ∈ U`. With
  `N(ū) log q = -log δ_0(m_0(ū))` these are the outer inequalities of Lemma II.3.4 for
  `P_0`, on `U = Ū ⊆ Ū_0`.
- `unipotentWeightIntegrable_of_levelSets`: assume `q > 1`, `N` measurable,
  `w(u) = q^{-N(u)/2}`, `σ ≥ 0`, `ν{u : σ(u) ≤ R} < ∞` for every `R`,
  `LevelSetMeasureBound ν N q` and `LevelHeightComparison U N q σ`. Then
  `UnipotentWeightIntegrable ν w σ`: `∫⁻_U ofReal(w(u) (1 + σ(u))^{-d}) dν(u) < ∞` for
  some real `d`.

Proof. Let `d'` be the exponent of II.4.1 and `d = max(d' + 2, 0)`. Split `U` into
`{N ≤ 0}` and the levels `{N = n + 1}`, `n ∈ ℕ`.

- On `{N ≤ 0}` the first inequality gives `1 + σ(u) ≤ C₀/C₁`, so this set lies in a
  sublevel set of `σ` and has finite measure; it also gives
  `N(u) ≥ (C₁ - C₀)/log q`, so `w` is bounded there, and `(1 + σ)^{-d} ≤ 1`. This is
  Waldspurger's "compact" part. The Lean proof does not use that `δ_0(m_0(ū)) ≤ 1`.
- On `{N = k}`, `k ≥ 1`, the second inequality and `1 + σ ≥ 1` give
  `1 + σ(u) ≥ c k` with `c = log q / (C₂ + |C₀|) > 0`, so
  `w(u) (1 + σ(u))^{-d} ≤ q^{-k/2} (c k)^{-d}`. With Lemma II.4.1 the integral over the
  level is at most `max(C, 0) c^{-d} k^{d' - d}`, and `∑ k^{d'-d}` converges because
  `d' - d ≤ -2`.

For the bound on `Ū(n)` the article cites Lemma II.4.1 and Lemma II.3.3. The Lean proof
uses Lemma II.4.1 and the second inequality of Lemma II.3.4 (`LevelHeightComparison`),
which is what gives `(1 + σ(ū))^{-d} ≤ (c n)^{-d}` on `Ū(n)`.

## Open obligations

For Waldspurger's data none of the following is proved here: the Iwasawa decomposition
`G = P_0 K`, the compact open `H` with its Iwahori factorization and the inclusions
`m^{-1}(H ∩ Ū_0) m ⊂ K` (II.1.1, lower bound); the upper bound of Lemma II.1.1
(Proposition I.4.3); the Cartan decomposition I.1 (4); Lemmas II.3.2 and II.3.4 (from the
representation `τ_P` of II.2); Lemma II.4.1 (from the formula for `Ξ` on `A_M`, II.4 (2),
and Lemma II.1.1); measurability of `N`, the identity `δ_0(m_0(ū)) = q^{-N(ū)}`, and
finiteness of the Haar measure of the sublevel sets of `σ` on `Ū`.
