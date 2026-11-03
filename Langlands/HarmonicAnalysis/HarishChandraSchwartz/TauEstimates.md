# Lemmas II.3.2, II.3.3 and II.3.4 from the properties of `τ_P`

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TauEstimates`, namespace
`Langlands.HarishChandraSchwartz`. It imports the published modules `SphericalBounds`
(`CartanWeightComparison`, `LevelHeightComparison`) and `SphericalLevi`
(`leviComponent`), and through them `ConstantTermBound` (`SigmaProductBound`) and
`Spherical` (`IsIwasawaPair`, `iwasawaFactor`, `exists_iwasawaFactor`, `iwasawaWeight`,
`iwasawaWeight_mul`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- II.2 (printed pp. 253–254, PDF pp. 19–20): for a standard `P = M U` there are a finite
  dimensional `E_P` with basis `(e_i)` and an algebraic representation `τ_P` of `G` with
  (1) `τ_P(m u) e_1 = δ_P^{alg}(m) e_1` for `m ∈ M`, `u ∈ U`, where
  `δ_P(m) = |δ_P^{alg}(m)|_F`; (2) `τ_P(a) e_i = δ_P^{alg}(a) χ_i(a) e_i` for `a ∈ A_0`;
  (3) `-Re(χ_i) ∈ C_i α_i + ā^{G*+}_0` for `i ≥ 2`; (4) `ū ↦ τ_P(ū) e_1` is injective on
  `Ū` with values in `e_1 + E'_P`. With `‖e‖ = sup_i |x_i|_F`: (5)
  `C_1 ‖e‖ ≤ ‖τ_P(k) e‖ ≤ C_2 ‖e‖` for `k ∈ K`; (6)
  `C_1 (1 + log ‖τ_P(ū) e_1‖) ≤ 1 + σ(ū) ≤ C_2 (1 + log ‖τ_P(ū) e_1‖)` for `ū ∈ Ū`.
- Lemma II.3.2 (printed p. 255, PDF p. 21): there is `C > 0` with
  `δ_0(m) ≤ C δ_0(m_0(g))` for `m ∈ M̄⁺_0` and `g ∈ K m K`. Proof: a compact `Γ ⊂ M_0` with
  `M̄⁺_0 ⊂ Γ Ā⁺_0`; `C_1` with `‖τ_0(h^{-1}) e‖ ≤ C_1 ‖e‖` for `h ∈ K ∪ KΓ`; for
  `u_0(g) m_0(g) = h a k` (`a ∈ Ā⁺_0`, `h ∈ KΓ`, `k ∈ K`),
  `δ_0(m_0(g))^{-1} = ‖τ_0(m_0(g)^{-1} u_0(g)^{-1}) e_1‖ ≤ C_1 ‖τ_0(a^{-1} h^{-1}) e_1‖
  ≤ C_1 δ_0(a)^{-1} ‖τ_0(h^{-1}) e_1‖ ≤ C_1^2 δ_0(a)^{-1}`, and
  `δ_0(a)^{-1} ≤ δ_0(m)^{-1} sup_Γ δ_0`.
- Lemma II.3.3 (printed p. 256, PDF p. 22): there is `C > 0` with
  `1 + σ(a p a^{-1}) ≤ C (1 + σ(p))` for `a ∈ Ā⁺_0`, `p ∈ P_0`. Proof: exchanging `P_0` and
  `P̄_0`, it suffices to bound `1 + σ(a^{-1} p̄ a)` for `p̄ = m ū ∈ P̄_0`; then
  `σ(a^{-1} p̄ a) ≤ σ(m) + σ(a^{-1} ū a)`, II.2 (6),
  `‖τ_0(a^{-1} ū a) e_1‖ ≤ ‖τ_0(ū) e_1‖`, II.2 (6) again, and Lemma II.3.1.
- Lemma II.3.4 (printed pp. 256–257, PDF pp. 22–23): there are `C_0, …, C_3 > 0` with
  `C_1 (1 + σ(ū)) ≤ C_0 - log δ_P(m_P(ū)) ≤ C_2 (1 + σ(m_P(ū))) ≤ C_2 (1 + σ(ū))` for
  `ū ∈ Ū`. Proof: `-log δ_P(m) ≤ C_4 (1 + σ(m))` (`δ_P^{alg}` is polynomial on `M`);
  Lemma II.3.1 and `σ(u_P m_P) = σ(ū)`; and
  `τ_P(ū^{-1}) e_1 = δ_P^{alg}(m_P(ū))^{-1} τ_P(k_P(ū)^{-1}) e_1` with II.2 (5), (6).

## Scope: abstract data and explicit hypotheses

The representations `τ_P`, the spaces `E_P`, the norms and the characters `χ_i` are not
constructed. The module uses only the functions `N(g) = ‖τ(g) e_1‖` and
`ψ(g) = log ‖τ(g) e_1‖` and states the consequences of II.2 that the proofs use as
explicit hypotheses on them. The groups are subgroups of an arbitrary group `G`, with
the Iwasawa data of `Spherical` (`hPK : IsIwasawaPair P K`, a character `δ` of `P`, and
for II.3.4 a Levi projection `m_P : P →* M` with a character `δ` of `M`). For
Waldspurger's data each hypothesis below is a consequence of II.2 (1)–(6) (and of the
polynomiality of `δ_P^{alg}`, II.3.1, and the properties of `σ` from I.1), as indicated.
All of these are open prerequisites of this generic unit, and none of them is treated as
a permitted structural exception. In particular II.2 is in-book: the representation
`τ_P` is constructed on printed p. 253 (on the space of polynomials `Q` on `G` with
`Q(m ū g) = δ_P^{alg}(m) Q(g)`), and the height comparison (6) is proved on p. 254 from the
polynomial estimates (7) and (8), with the algebraic facts cited from Humphreys [H]
(Exercise 8 p. 115: orbits of unipotent groups on affine varieties are closed; Theorem
4.6). The comparison (6) and the other
derived bounds therefore remain proof obligations; if a single algebraic input among them
is later kept external, it must be identified with a precise entry of the Renard
Chapter V structural ledger.

## Definitions

- `ModulusHeightBounds U σ ℓ δ : Prop`, for `ℓ : G → M` and `δ : M →* ℝ≥0ˣ`: there are
  real `C₀` and `C₁, C₂, C₃ > 0` with
  `C₁ (1 + σ(u)) ≤ C₀ - log δ(ℓ(u)) ≤ C₂ (1 + σ(ℓ(u)))` and
  `1 + σ(ℓ(u)) ≤ C₃ (1 + σ(u))` for all `u ∈ U`. With `ℓ = m_P` and `δ = δ_P` this is the
  conclusion of Lemma II.3.4 (with Waldspurger's last constant written `C₂ C₃`).

## Results

- `cartanWeightComparison_of_norm` (Lemma II.3.2). Hypotheses, for `N : G → ℝ`, sets
  `S ⊆ G` and `Γ, A ⊆ P`: `δ` trivial on `P ∩ K` (`hδ`); `N(p^{-1}) = δ(p)^{-1}` for
  `p ∈ P` (II.2 (1) with `‖e_1‖ = 1`); `N(k y) ≤ C N(y)` for `k ∈ K` (II.2 (5));
  `N(a^{-1} y) ≤ δ(a)^{-1} N(y)` for `a ∈ A` (II.2 (2), (3): `a^{-1}` acts on `e_i` by
  `δ^{alg}(a)^{-1} χ_i(a)^{-1}` with `|χ_i(a)^{-1}| ≤ 1` on `Ā⁺_0`); `N((k γ)^{-1}) ≤ C`
  for `k ∈ K`, `γ ∈ Γ` (II.2 (5) on `K Γ`); `δ(γ) ≤ C` for `γ ∈ Γ`; every `s ∈ S` is
  `γ a` with `γ ∈ Γ`, `a ∈ A`. Conclusion: `CartanWeightComparison K S φ` for
  `φ = iwasawaWeight hPK δ` (`φ(p k) = δ(p)^{1/2}`), that is
  `φ(s) ≤ C φ(k₁ s k₂)`; squaring gives Waldspurger's `δ_0(s) ≤ C^2 δ_0(m_0(k₁ s k₂))`.
- `conj_height_le_of_tau` (Lemma II.3.3, for `P̄_0`). Hypotheses, for subgroups `M`, `U`,
  a set `T` and `ψ, σ : G → ℝ`: `C₁ (1 + ψ(u)) ≤ 1 + σ(u) ≤ C₂ (1 + ψ(u))` on `U`
  with `C₁, C₂ > 0` (II.2 (6)); `a^{-1} u a ∈ U` and `ψ(a^{-1} u a) ≤ ψ(u)` for `a ∈ T`,
  `u ∈ U` (II.2 (2), (3)); `a m = m a` for `a ∈ T`, `m ∈ M`; `SigmaProductBound M U σ`
  (Lemma II.3.1); `σ ≥ 0`; `σ(x y) ≤ σ(x) + σ(y)`. Conclusion: there is `C` with
  `1 + σ(a^{-1} m u a) ≤ C (1 + σ(m u))` for `a ∈ T`, `m ∈ M`, `u ∈ U`. With
  `M U = M_0 Ū_0` and `T = Ā⁺_0` this is the form of Lemma II.3.3 that Waldspurger proves;
  his statement for `P_0` is the same lemma for the opposite data.
- `modulusHeightBounds_of_tau` (Lemma II.3.4). Hypotheses, for `ψ, σ : G → ℝ`:
  `1 + σ(u) ≤ C (1 + ψ(u))` on `U` with `C > 0` (II.2 (6), upper inequality);
  `ψ((p k)^{-1}) ≤ C - log δ(m_P(p))` for `p ∈ P`, `k ∈ K` (II.2 (1), (5));
  `-log δ(m) ≤ C (1 + σ(m))` on `M` (polynomiality of `δ_P^{alg}`);
  `1 + σ(m_P(p)) ≤ C (1 + σ(p))` on `P` (from Lemma II.3.1); `σ(g k) = σ(g)` for `k ∈ K`;
  `σ(g^{-1}) = σ(g)`; `σ ≥ 0`. Conclusion:
  `ModulusHeightBounds U σ (leviComponent hPK mP) δ`.
- `ModulusHeightBounds.levelHeightComparison`: if `-log δ(ℓ(u)) = N(u) log q` on `U`, then
  `LevelHeightComparison U N q σ` (the hypothesis of Lemma II.4.2 in `SphericalBounds`),
  with constants `C₀`, `C₁` and `C₂ C₃`.

## Proof notes

The proofs follow Waldspurger's.

- II.3.2. For `g = k₁ s k₂` with `s = γ a`, write `g = p k` (`iwasawaFactor`); then
  `p^{-1} = (k k₂^{-1}) a^{-1} (k₁ γ)^{-1}`, so
  `δ(p)^{-1} = N(p^{-1}) ≤ C_K δ(a)^{-1} C_Γ`. With `δ(s) = δ(γ) δ(a) ≤ C_δ δ(a)` this gives
  `δ(s) ≤ C_K C_Γ C_δ δ(p)`, and the weights are `φ(s) = δ(s)^{1/2}`,
  `φ(g) = δ(p)^{1/2}` (`iwasawaWeight_mul`). The constant `C_K` is nonnegative because
  `N(1) = 1`.
- II.3.3. `a^{-1} m u a = m (a^{-1} u a)`; subadditivity, the two inequalities of
  II.2 (6) and the contraction give
  `1 + σ(a^{-1} m u a) ≤ (1 + σ(m)) + (C₂/C₁)(1 + σ(u)) ≤ 2 (1 + C₂/C₁) (1 + sup(σ(m), σ(u)))`,
  and Lemma II.3.1 bounds the last factor by `C^{-1} (1 + σ(m u))`.
- II.3.4. With `u = p k`: `1 + σ(u) = 1 + σ(u^{-1}) ≤ C₆ (1 + ψ(u^{-1}))
  ≤ C₆ (1 + C_ψ - log δ(m_P(p)))`, giving the first inequality with `C₀ = 1 + C_ψ`; the
  second from the polynomiality bound with `C₂ = |C₀| + |C₄| + 1`; the third from the
  Levi bound and `σ(u) = σ(p)`, with `C₃ = max(C₅, 1)`.

## Open obligations

For Waldspurger's group none of the hypotheses is proved here. Open proof obligations:
the construction of `τ_P` with II.2 (1)–(5) (p. 253); the height comparison II.2 (6)
(p. 254, from (7), (8) and the facts cited from [H]); the bounds on `N` and `ψ` derived from
II.2; the compact set `Γ` with `M̄⁺_0 ⊂ Γ Ā⁺_0`; the polynomiality bound for
`δ_P^{alg}`; Lemma II.3.1 for Waldspurger's `σ`; and the properties of `σ`. Lemma II.3.5 is not formalized here.
