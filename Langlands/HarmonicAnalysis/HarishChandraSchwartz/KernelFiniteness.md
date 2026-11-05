# Proposition VIII.4.1: finiteness of `p_χ(°C_H)` (abstract assembly)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelFiniteness`, namespace
`Langlands.HarishChandraSchwartz`. It imports `KernelQuotient` (`IsKernelAlphaChiSpace`,
`finiteDimensional_of_kernelAlphaChi`; through it `KernelReproduction`, `CentralProjection`
and the published `QuotientMeasure` with `LeftQuotient` and `IsCompatible`), `KernelDiagonal`
(`productSet`, `centralCharacterExtension`, `diagonalWeight`,
`integral_conj_mul_eq_indicator`, `integrable_re_kernelAlphaChi_diag`) and
`CuspidalIntegrability` (`conjFun`, `lintegral_lt_top_of_conjugationIntegralBound`; through it
`CuspidalDecay` with `ConjugationIntegralBound`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- Proposition VIII.4.1, printed p. 327 (PDF p. 93): "Pour tout sous-groupe ouvert compact `H`
  de `G` et tout `χ ∈ Â_G`, l'espace `p_χ(°C_H)` est de dimension finie."
- Its proof, printed pp. 328–330 (PDF pp. 94–96): formula (1),
  `(α_χ(·, g), f)_{A_G\G} = f(g)` for `f ∈ p_χ(°C_H)`; an orthonormal basis `(f_i)` of the span
  `F` of the `α_χ(·, g)` gives `α_χ(g₁, g₂) = Σ f_i(g₁) conj(f_i(g₂))`, so
  `∫_{A_G\G} α_χ(g, g) dg` converges if and only if the basis is finite; "par définition, pour
  tout `g ∈ G`, `α_χ(g, g) = ∫_G °e(g⁻¹ g' g) ψ(g') dg'`"; "Comme `°e` est à support dans `G¹`,
  on peut remplacer `ψ` par le produit `ϕ` de `ψ` par la fonction caractéristique de `G¹`.
  Alors `∫_{A_G\G} α_χ(g, g) dg = ∫_{A_G\G} ∫_G °e(g⁻¹ g' g) ϕ(g') dg' dg`." (p. 329); "Comme
  `ϕ ∈ C(G)` et `°e ∈ °C(G)`, cette expression est convergente d'après le Corollaire III.3.2"
  (p. 330; the statement used is Corollary VIII.3.2); then `F` is finite dimensional and, by
  (1), equals `p_χ(°C_H)`.
- Corollary VIII.3.2, printed p. 326 (PDF p. 92): for `f₁ ∈ °C(G)` and `f₂ ∈ C(G)`,
  `∫_{A_G\G} |∫_G f₁(h g h⁻¹) f₂(g) dg| dh < ∞`.

Waldspurger's diagonal integrand is the integrand of Corollary VIII.3.2 at `h = g⁻¹`. This
module makes that evaluation explicit and assembles the published steps of the
proof into one statement, with the analytic inputs as hypotheses.

## Scope: abstract data and explicit hypotheses

- `out_inv_mul_mul_out`: `G` a group, `A` a subgroup, `hAc : A ≤ Subgroup.center G`, and
  `hq : Quotient.mk _ g = q` for `q : LeftQuotient A`.
- `lintegral_conj_out_lt_top`: `G` a group with a measurable structure and `[MeasurableMul G]`,
  a left and right invariant measure `μ` on `G`, a subgroup `A` with `hAc`, a measure `ν` on
  `LeftQuotient A` (any measurable structure), and the hypotheses of
  `lintegral_lt_top_of_conjugationIntegralBound` for the map `h ↦ ⟦h⁻¹⟧`: a subgroup `M`, a set
  `T ⊆ M`, `e : M → ℝ` with `he : ∀ a ∈ T, 0 < e a`, `σ : G → ℝ` with `hσ : ∀ g, 0 ≤ σ g`,
  `f₁ f₂ : G → ℂ`, a countable index type `ι`, cells `Ω : ι → Set (LeftQuotient A)` with
  `hcover : ∀ q, ∃ i, q ∈ Ω i`, `a : ι → M` with `haT : ∀ i, a i ∈ T`, sets `K' Y ⊆ G` with
  `hcell : ∀ i, ∀ q ∈ Ω i, ∃ k ∈ K', ∃ y ∈ Y, q = ⟦(k a_i y)⁻¹⟧`, `hfin₁`: the conjugates
  `conjFun k f₁` (`k ∈ K'`) form a finite set, `hfin₂`: the conjugates `conjFun y⁻¹ f₂`
  (`y ∈ Y`) form a finite set, `h31 : ∀ k ∈ K', ∀ y ∈ Y, ConjugationIntegralBound μ T
  (conjFun k f₁) (conjFun y⁻¹ f₂) e σ` (Proposition VIII.3.1 for these pairs),
  `hm : ∀ i, ν (Ω i) ≤ ENNReal.ofReal (C₂ * (e (a i) ^ 2)⁻¹)`, and
  `hsum : Summable fun i => (1 + σ (a i)) ^ (-r)` for one `r`.
- `finiteDimensional_of_conjugationIntegralBound`: the setting of `KernelQuotient`: `G` a
  Hausdorff, locally compact, second countable topological group with its Borel structure;
  `μG` finite on compacts, s-finite, left and right invariant, with `[MeasurableMul A]`;
  `A` a closed subgroup (`hA`) with its Borel structure and a measure `μA` that is s-finite,
  left and right invariant, inversion invariant and finite on compacts, with
  `[MeasurableInv A]`; `LeftQuotient A` with its Borel structure and `ν` with
  `hν : IsCompatible A μG μA ν`; `χ : A →* ℂˣ`; `H` a subgroup with an s-finite measure `μH`;
  `E : G → ℂ`. Its hypotheses are:
  - from `finiteDimensional_of_kernelAlphaChi`: `hAc : A ≤ Subgroup.center G`,
    `hχ : IsUnitaryCharacter χ`, `hE : ∀ x, conj (E x) = E x`,
    `hmes : (μH Set.univ).toReal ≠ 0`, `hV : IsKernelAlphaChiSpace μG μA χ μH E V`,
    `hKV : ∀ y, (fun g => kernelAlphaChi μA χ μH E g y) ∈ V`, and
    `hprod : ∀ f ∈ V, ∀ f' ∈ V, Integrable (fun q => f q̇ * conj (f' q̇)) ν`;
  - from `integrable_re_kernelAlphaChi_diag` (with `s = Quotient.out`):
    `hH : IsOpen (H : Set G)`, `hμH : μH.map Subtype.val = μG.restrict H`,
    `hχH : ∀ a : A, (a : G) ∈ H → χ a = 1`, `hfin : μA {a : A | (a : G) ∈ H} ≠ ⊤`,
    `hint : ∀ q, Integrable (fun x => E (q̇⁻¹ * x * q̇) * centralCharacterExtension A H χ x)
    (μG.restrict (productSet A H))`, and `hmeas`: `q ↦ α_χ(q̇, q̇)` is a.e. strongly
    measurable for `ν`;
  - the support of `E`: a normal subgroup `N` (for `G¹`) with `hEN : ∀ x, x ∉ N → E x = 0`;
  - the hypotheses of `lintegral_conj_out_lt_top` for `f₁ = E` and
    `f₂ = diagonalWeightOn A N μA χ μH`, with `μ = μG`: `M`, `T`, `e`, `σ`, `he`, `hσ`, `ι`,
    `Ω`, `hcover`, `a`, `haT`, `K'`, `Y`, `hcell`, `hfin₁`, `hfin₂`, `h31`, `C₂`, `hm`, `r`,
    `hsum`.

Here `q̇` is `Quotient.out q`, and `⟦x⟧` is the class `A x` of `x : G` in `LeftQuotient A`
(cosets `A x`); for central `A` this quotient is Waldspurger's `A_G \ G`.

## Definitions

- `diagonalWeightOn A N μA χ μH : G → ℂ` is `(N : Set G).indicator (diagonalWeight A μA χ μH)`:
  Waldspurger's `ϕ`, the product of `ψ` (`diagonalWeight`: `ψ(a h) = χ(a) mes(A_G ∩ H)
  mes(H)⁻²` on `A_G H`, `0` outside) with the characteristic function of `N` (his `G¹`).

## Results

- `out_inv_mul_mul_out`: for central `A` and `q = A g`, `q̇⁻¹ x q̇ = g⁻¹ x g` for every `x`.
- `lintegral_conj_out_lt_top` (**Corollary VIII.3.2 at `h = g⁻¹`**):
  `∫⁻_{A\G} ‖∫_G f₁(q̇⁻¹ g q̇) f₂(g) dμ(g)‖ₑ dν(q) < ∞`.
- `finiteDimensional_of_conjugationIntegralBound` (**Proposition VIII.4.1 in abstract form**):
  `FiniteDimensional ℂ V`.

## Proof notes

- `out_inv_mul_mul_out`: `Quotient.mk_out` gives `b = g q̇⁻¹ ∈ A`, so `q̇ = b⁻¹ g`; since `b` is
  central, `(b⁻¹ g)⁻¹ x (b⁻¹ g) = g⁻¹ b x b⁻¹ g = g⁻¹ x g`.
- `lintegral_conj_out_lt_top`: apply `lintegral_lt_top_of_conjugationIntegralBound` with the
  projection `π(h) = ⟦h⁻¹⟧` and `F(q) = ‖∫ f₁(q̇⁻¹ g q̇) f₂(g) dμ‖ₑ`. Its hypothesis
  `F(π h) = ‖∫ f₁(h g h⁻¹) f₂(g) dμ‖ₑ` is `out_inv_mul_mul_out` with `g = h⁻¹`, and its cell
  hypothesis for `π` is `hcell`. No change of variables on the quotient is used.
- `finiteDimensional_of_conjugationIntegralBound`: `finiteDimensional_of_kernelAlphaChi`
  reduces to the integrability of `q ↦ Re α_χ(q̇, q̇)`, which
  `integrable_re_kernelAlphaChi_diag` reduces to
  `∫⁻ ‖∫_G E(q̇⁻¹ x q̇) ψ(x) dμG‖ₑ dν < ∞`. `integral_conj_mul_eq_indicator` (with `hEN`)
  replaces `ψ` by `ϕ = diagonalWeightOn A N μA χ μH`, and `lintegral_conj_out_lt_top` with
  `f₁ = E`, `f₂ = ϕ` concludes.

## Relation to the Library

- `finiteDimensional_of_kernelAlphaChi` (`KernelQuotient`) is Proposition VIII.4.1 with the
  integrability of the diagonal as a hypothesis; this module replaces that hypothesis by the
  hypotheses of Corollary VIII.3.2 (`CuspidalIntegrability`) through the diagonal computation
  of `KernelDiagonal`.
- `lintegral_lt_top_of_conjugationIntegralBound` is Corollary VIII.3.2 for an arbitrary
  projection `π`; `lintegral_conj_out_lt_top` is its instance at `π(h) = ⟦h⁻¹⟧` for central
  `A`. No other Library declaration evaluates the Corollary at `h = g⁻¹`.

## Open obligations

The definitions of `°e`, `°C(G)` and `°C_H` (VIII.2, depending on Theorem VII.2.5), and for
Waldspurger's data the verification of `IsKernelAlphaChiSpace` for `p_χ(°C_H)` (Lemma VIII.2.3
and the absolute convergence of the triple integrals), `hKV`, `hprod`, `hint`, `hmeas`, the
support of `°e` in `G¹`, and the hypotheses of Corollary VIII.3.2 for `f₁ = °e`, `f₂ = ϕ`
(Proposition VIII.3.1 for the conjugates, `ϕ ∈ C(G)`, finiteness of the conjugates under the
compact sets, and the summability over the lattice), are not proved here. In the application
the cells are the images in `A_G\G` of the sets `(K a Γ K)⁻¹`; their measure bound
`hm` would follow from I.1 (5) and the invariance of the measure on `A_G\G` under inversion,
which are not proved here. The comparison of `ν` with Waldspurger's normalization of the
measure on `A_G\G` and of `μH` with the restriction of the Haar measure of `G` is not made
here.
