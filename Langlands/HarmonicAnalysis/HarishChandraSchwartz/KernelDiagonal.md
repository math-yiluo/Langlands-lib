# The diagonal of `α_χ` (Waldspurger VIII.4.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelDiagonal`, namespace
`Langlands.HarishChandraSchwartz`. It imports `KernelReproduction` (`kernelAlpha`,
`kernelAlphaChi`, `kernelAlphaChi_eq`). From Mathlib it uses Tonelli's and Fubini's theorems
(`lintegral_prod`, `lintegral_lintegral_swap`, `integral_prod`), `lintegral_mul_left_eq_self`,
`measure_preimage_mul`, `integral_map`, `integrable_map_measure`, `integral_smul_measure` and
`setIntegral_eq_integral_of_forall_compl_eq_zero`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

Proof of Proposition VIII.4.1, printed p. 329 (PDF p. 95):

- "Comme `ϕ ∈ °C_H`, on a, d'après le Lemme VIII.2.3, `ϕ * °e = ϕ * e = mes(H) ϕ`", where `e`
  is the characteristic function of `H`.

- "Or, par définition, pour tout `g ∈ G`, `α_χ(g, g) = ∫_G °e(g⁻¹ g' g) ψ(g') dg'`, où `ψ` est
  la fonction sur `G` définie par `ψ(g) = 0` si `g ∉ A_G H`,
  `ψ(a h) = χ(a) mes(A_G ∩ H) mes(H)⁻²` si `a ∈ A_G`, `h ∈ H`."
- "Comme `°e` est à support dans `G¹`, on peut remplacer `ψ` par le produit `ϕ` de `ψ` par la
  fonction caractéristique de `G¹`. Alors `∫_{A_G\G} α_χ(g, g) dg =
  ∫_{A_G\G} ∫_G °e(g⁻¹ g' g) ϕ(g') dg' dg`", whose convergence is Corollary VIII.3.2 (printed
  "Corollaire III.3.2" on p. 330).

Waldspurger states the first identity "by definition". Its proof here is a derived step: the
integral over `A_G × H` in `α_χ(g, g)` is transported to `A_G H` by the product formula below.

## Scope: abstract data and explicit hypotheses

`G` is a second countable topological group with its Borel structure. `A` and `H` are
subgroups of `G`; `A` carries a measurable structure in which open sets are measurable
(`[OpensMeasurableSpace A]`), and `[MeasurableMul A]`. `μ_G` is a left-invariant s-finite
measure on `G`, `μ_A` a left-invariant s-finite measure on `A`, and `μ_H` an s-finite measure on
`H` (with the measurable structure induced from `G`). The hypotheses of each result:

- `isOpen_productSet`: `hH : IsOpen (H : Set G)`; `mul_mem_productSet`: none.
- `convolution_indicator_eq`: left invariance of `μ_G`, `hH : MeasurableSet (H : Set G)` and
  `hφ : ∀ x, ∀ h ∈ H, φ (x * h) = φ x` (right invariance of `φ`); no second countability.
- `convolution_eq_of_convolution_eq_indicator`: those, `hμH : μH.map Subtype.val = μG.restrict H`
  and `hE : ∀ x, convolution μG φ E x = convolution μG φ 1_H x` (Waldspurger's `φ * °e = φ * e`,
  Lemma VIII.2.3).
- `measure_inv_mul_mem_eq`: `[MeasurableMul A]`, left invariance of `μ_A`, `g ∈ A H`.
- `lintegral_prod_mul_eq`, `map_prod_mul_eq`: `hH`, the measures above, and
  `hμH : μH.map Subtype.val = μG.restrict H` (`μ_H` is the restriction of `μ_G` to `H`; for
  Waldspurger `dh` is the Haar measure of `G` restricted to `H`, so `mes(H) = μ_G(H)`); the
  first also a measurable `f ≥ 0`.
- `integral_prod_mul_eq`: those and `hF : AEStronglyMeasurable F (μG.restrict (A H))`.
- `integrable_prod_mul`: those, `hfin : μA (A ∩ H) ≠ ⊤` and `Integrable F (μG.restrict (A H))`.
- `centralCharacterExtension_mul`: `hχH : ∀ a : A, (a : G) ∈ H → χ a = 1` (`χ` is trivial on
  `A ∩ H`; Waldspurger reduces to this case at the start of the proof, and the published
  `centralProjection_eq_zero_of_ne_one` covers the other case).
  `centralCharacterExtension_eq_zero`: `x ∉ A H`.
- `kernelAlphaChi_diag_eq`: `[MeasurableMul A]`, `[MeasurableInv A]`, left and inversion
  invariance of `μ_A`, `hH`, `hμH`, `hAc : A ≤ Subgroup.center G`, `hχH`, `hfin`, and
  `hint : Integrable (fun x => E(g⁻¹ x g) ψ̃(x)) (μG.restrict (A H))` at the point `g`.
- `integral_conj_mul_eq_indicator`: a normal subgroup `N` (for `G¹`) and
  `hE : ∀ x, x ∉ N → E x = 0`.
- `integrable_re_kernelAlphaChi_diag`: those of `kernelAlphaChi_diag_eq`, a measure space
  `(X, ν)` with a map `s : X → G` (in the application `X = A_G \ G` and `s = Quotient.out`),
  `hint` at every `s q`, `hmeas : AEStronglyMeasurable (fun q => α_χ(s q, s q)) ν` and
  `hfinite : ∫⁻ q, |∫_G E((s q)⁻¹ x (s q)) ψ(x) dμ_G(x)| dν(q) < ∞`.

## Definitions

- `productSet A H = {g | ∃ a ∈ A, a⁻¹ g ∈ H}`, the set `A H`.
- `centralCharacterExtension A H χ : G → ℂ`, written `ψ̃`: `ψ̃(x) = χ(a)` for a chosen `a ∈ A`
  with `a⁻¹ x ∈ H` if `x ∈ A H`, and `ψ̃(x) = 0` otherwise.
- `diagonalWeight A μA χ μH : G → ℂ`, Waldspurger's `ψ`:
  `ψ = μ_A(A ∩ H) · mes(H)⁻² · ψ̃`, with `mes(H) = (μH Set.univ).toReal`, so that
  `ψ(a h) = χ(a) mes(A ∩ H) mes(H)⁻²` on `A H` (by `centralCharacterExtension_mul`) and `ψ = 0`
  outside.

## Results

- `isOpen_productSet`: `A H` is open when `H` is.
- `convolution_indicator_eq` (**`φ * e = mes(H) φ`**): `(φ * 1_H)(x) = μ_G(H) φ(x)`.
- `convolution_eq_of_convolution_eq_indicator`: under `hE`, `(φ * E)(x) = mes(H) φ(x)` with
  `mes(H) = (μH Set.univ).toReal`; this is the hypothesis `hconv` of
  `integral_conj_kernelAlphaChi_mul` (`KernelReproduction`).
- `measure_inv_mul_mem_eq`: for `g ∈ A H`, `μ_A{a | a⁻¹ g ∈ H} = μ_A(A ∩ H)`.
- `lintegral_prod_mul_eq` (**product formula**): `∫_{A × H} f(a h) d(μ_A × μ_H) =
  μ_A(A ∩ H) ∫_{A H} f dμ_G` for measurable `f ≥ 0`.
- `map_prod_mul_eq`: the image of `μ_A × μ_H` under `(a, h) ↦ a h` is
  `μ_A(A ∩ H) • μ_G|_{A H}`.
- `integral_prod_mul_eq`, `integrable_prod_mul`: the same for complex-valued `F`.
- `centralCharacterExtension_mul`: `ψ̃(a h) = χ(a)` if `χ` is trivial on `A ∩ H`;
  `centralCharacterExtension_eq_zero`: `ψ̃ = 0` off `A H`.
- `kernelAlphaChi_diag_eq` (**the diagonal of `α_χ`**):
  `α_χ(g, g) = ∫_G E(g⁻¹ x g) ψ(x) dμ_G(x)`.
- `integral_conj_mul_eq_indicator` (**support in `G¹`**): if `E` vanishes off the normal
  subgroup `N`, `∫_G E(g⁻¹ x g) ψ(x) dx = ∫_G E(g⁻¹ x g) 1_N(x) ψ(x) dx`.
- `integrable_re_kernelAlphaChi_diag`: under `hmeas` and `hfinite`, `q ↦ Re α_χ(s q, s q)` is
  `ν`-integrable; this is the diagonal hypothesis `hint` of
  `IsSectionReproducingKernel.finiteDimensional` for `K(y) = α_χ(·, y)`.

## Proof notes

- `φ * e = mes(H) φ`: `(φ * 1_H)(x) = ∫ φ(h) 1_H(h⁻¹ x) dh`; on `{h | h⁻¹ x ∈ H} = x H` right
  invariance gives `φ(h) = φ(x)`, and `μ_G(x H) = μ_G(H)` by left invariance
  (`measure_preimage_mul`). For the second lemma, `μ_H(H) = μ_G(H)` follows from `hμH`.

- Product formula. Tonelli on `A × H`; for fixed `a`, `∫_H f(a h) dμ_H = ∫_G 1_H(x) f(a x) dμ_G
  = ∫_G 1_{a H}(y) f(y) dμ_G` by `hμH` and left invariance of `μ_G`. Exchanging the integrals
  (`lintegral_lintegral_swap`) gives `∫_G f(y) μ_A{a | a⁻¹ y ∈ H} dμ_G(y)`. For `y = a₀ h₀ ∈ A H`
  the set `{a | a⁻¹ y ∈ H}` is the left translate `a₀ (A ∩ H)`, of measure `μ_A(A ∩ H)` by left
  invariance of `μ_A` (`measure_preimage_mul`); for `y ∉ A H` it is empty. No Haar uniqueness,
  centrality or compactness is used.
- The measure identity follows by applying the product formula to indicators; the integral
  form and the integrability transfer follow from `integral_map`, `integrable_map_measure`
  and `integral_smul_measure`.
- `centralCharacterExtension_mul`: if `a'` is the chosen representative of `a h`, then
  `a'⁻¹ a ∈ A ∩ H`, so `χ(a') = χ(a)`.
- Diagonal. By `kernelAlphaChi_eq`, `α_χ(g, g) = ∫_A χ(a) α(g, a g) da =
  mes(H)⁻² ∫_A ∫_H χ(a) E(g⁻¹ h a g) dh da`. Since `a` is central and `ψ̃(a h) = χ(a)`, the
  integrand is `Φ(a h)` with `Φ(x) = E(g⁻¹ x g) ψ̃(x)`. Fubini (`integrable_prod_mul` from
  `hint`) and `integral_prod_mul_eq` give `mes(H)⁻² μ_A(A ∩ H) ∫_{A H} Φ dμ_G`, and `Φ = 0` off
  `A H`.
- Support in `G¹`: for `x ∉ N`, `g⁻¹ x g ∉ N` by normality, so `E(g⁻¹ x g) = 0`.
- Integrability: `α_χ(s q, s q)` equals the integral in `hfinite` for every `q`, so its norm
  has finite integral; with `hmeas` it is integrable, and so is its real part.

## Relation to the Library

- `KernelReproduction` defines `α` and `α_χ`; `kernelAlphaChi_eq` is used here.
- `CuspidalIntegrability` (`lintegral_lt_top_of_conjugationIntegralBound`, Corollary VIII.3.2 in
  abstract form) bounds `∫ |∫_G f₁(h g h⁻¹) f₂(g) dg|` over a quotient. With `f₁ = °e`,
  `f₂ = 1_{G¹} ψ` and `h = (s q)⁻¹` its integrand is that of `hfinite`; the passage from `h` to
  `h⁻¹` on `A_G \ G` is not made here.
- The Library's quotient-measure modules (`QuotientWeilKernel`, `StandardIntertwining*`) compare
  measures on quotients by closed subgroups; none states the product formula for `A × H → A H`
  with a non-injective multiplication map.

## Open obligations

The definitions of `°e` and `°C_H`, Lemma VIII.2.3 (the hypothesis `hE`), the integrability `hint` and the measurability `hmeas` for
Waldspurger's data, the identification of `μ_H` with the restriction of the Haar measure and of
`μ_A` with the Haar measure of `A_G`, finiteness `hfin` (compactness of `A_G ∩ H`), and the
application of Corollary VIII.3.2 (including the inversion `h ↦ h⁻¹` on `A_G \ G` and the
membership `1_{G¹} ψ ∈ C(G)`) are not proved here.
