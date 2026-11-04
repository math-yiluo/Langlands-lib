# Reproducing kernels read through a section (Waldspurger VIII.4.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SectionReproducingKernel`,
namespace `Langlands.HarishChandraSchwartz`. It imports only Mathlib: Euclidean spaces
(`stdOrthonormalBasis`, `OrthonormalBasis.sum_repr'`), orthogonal complements
(`Submodule.orthogonal_eq_bot_iff`) and the Bochner integral (`integral_re`,
`integral_conj`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Proposition VIII.4.1, printed p. 327 (PDF p. 93): for every compact open subgroup `H` and
  every `χ ∈ Â_G`, the space `p_χ(°C_H)` is finite dimensional. Here `p_χ(°C_H)` consists
  of functions `f` on `G` with `f(a g) = χ(a) f(g)` for `a ∈ A_G` (p. 327).
- Its proof, printed pp. 328–330 (PDF pp. 94–96):
  - p. 328: on `p_χ(°C_H)`, `(f₁, f₂)_{A_G\G} = ∫_{A_G\G} conj(f₁(g)) f₂(g) dg`, a positive
    definite hermitian product. The bar is on `f₁` (checked on the page image).
  - p. 328, formula (1): `(α_χ(·, g), f)_{A_G\G} = f(g)` for `f ∈ p_χ(°C_H)` and `g ∈ G`,
    where `α_χ(·, g) ∈ p_χ(°C_H)`.
  - p. 329: with `F` the span of the `α_χ(·, g)` and a countable orthonormal basis
    `(f_i)_{i∈I}` of `F`, (1) gives `α_χ(g₁, g₂) = Σ_i f_i(g₁) conj(f_i(g₂))` (bar on the
    second factor, checked on the page image); hence `∫_{A_G\G} α_χ(g, g) dg` converges if
    and only if `I` is finite.
  - p. 330: the convergence of this integral (Corollary VIII.3.2, printed "Corollaire
    III.3.2"), and the conclusion that `p_χ(°C_H) = F` is finite dimensional.

## Scope: abstract data and explicit hypotheses

The integrand `conj(f₁) f₂` of Waldspurger's product is invariant under `A_G` for unitary
`χ`, but `f₁` and `f₂` themselves are functions on `G`, not on `A_G\G`. This module
therefore reads the functions through a map. The data are:

- a measurable space `X` with a measure `μ` (in the application `A_G\G` with its quotient
  measure);
- a type `Y` (in the application `G`) and a map `s : X → Y` (in the application a section
  of `G → A_G\G`); no measurability of `s` is assumed;
- a submodule `V` of the complex functions `Y → ℂ` (in the application `p_χ(°C_H)`);
- a map `K : Y → V` (in the application `K(y) = α_χ(·, y)`).

The structure `IsSectionReproducingKernel μ s V K` bundles two hypotheses:

- `integrable`: for `f, g ∈ V`, `x ↦ f(s x) conj(g(s x))` is `μ`-integrable;
- `reproduce`: for `f ∈ V` and `y ∈ Y`, `∫ f(s x) conj(K(y)(s x)) dμ(x) = f(y)`, i.e.
  Waldspurger's formula (1) `(α_χ(·, y), f) = f(y)` read through `s`.

The finiteness results take the further hypothesis `hint`: `x ↦ Re K(s x)(s x)` is
`μ`-integrable (in the application, `Re α_χ(s x, s x)`; Waldspurger's convergence of
`∫ α_χ(g, g) dg`).

## Definitions

- `sectionForm μ s f g = ∫ f(s x) conj(g(s x)) dμ(x)` for `f, g : Y → ℂ`. Waldspurger's
  product is `(f₁, f₂)_{A_G\G} = sectionForm μ s f₂ f₁`.
- `IsSectionReproducingKernel μ s V K`, the structure above.
- `IsSectionReproducingKernel.Space hK`, a type synonym of `V` indexed by
  `hK : IsSectionReproducingKernel μ s V K`, with the linear equivalence
  `hK.toSpace : V ≃ₗ[ℂ] hK.Space` (the identity).
- `hK.preCore` and `hK.core`: the pre-inner product and inner product cores on `hK.Space`
  for `⟪f, g⟫ = sectionForm μ s g f`, i.e. Waldspurger's `(f, g)_{A_G\G}`.
- The resulting instances `NormedAddCommGroup hK.Space` and `InnerProductSpace ℂ hK.Space`.

## Results

All results in the namespace `IsSectionReproducingKernel` assume `hK`, except
`sectionForm_swap`, `sectionForm_smul_left` and `sectionForm_smul_right`, which hold for all
data.

- `sectionForm_swap`: `sectionForm μ s g f = conj (sectionForm μ s f g)`.
- `sectionForm_add_left`, `sectionForm_smul_left`, `sectionForm_add_right`,
  `sectionForm_smul_right`: sesquilinearity on `V`.
- `re_sectionForm_self`: `Re B(f, f) = ∫ |f(s x)|² dμ(x)`; `integrable_norm_sq`:
  `x ↦ |f(s x)|²` is integrable; `sectionForm_self_re_nonneg`: `0 ≤ Re B(f, f)`.
- `sectionForm_kernel`: `B(f, K y) = f(y)`.
- `inner_toSpace`: `⟪toSpace f, toSpace g⟫ = sectionForm μ s g f`;
  `inner_toSpace_kernel`: `⟪toSpace (K y), toSpace f⟫ = f(y)`.
- `norm_toSpace_sq`: `‖toSpace f‖² = ∫ |f(s x)|² dμ(x)`; `norm_toSpace_kernel_sq`:
  `‖toSpace (K y)‖² = Re K(y)(y)`.
- `sum_norm_sq_le` (Bessel's inequality at a point): for a finset `t` and `e : ι → V` with
  `toSpace ∘ e` orthonormal (hypothesis `he`), `Σ_{i ∈ t} |e_i(y)|² ≤ Re K(y)(y)`.
- `card_le_of_orthonormal`: under `hint`, every `e : Fin n → V` with `toSpace ∘ e`
  orthonormal has `n ≤ ∫ Re K(s x)(s x) dμ(x)`.
- `finrank_le_of_submodule`: under `hint`, every finite-dimensional submodule `E` of
  `hK.Space` has `dim E ≤ ∫ Re K(s x)(s x) dμ(x)`.
- `finiteDimensional` (Proposition VIII.4.1 in abstract form): under `hint`, `V` is finite
  dimensional.
- `finrank_le`: under `hint`, `dim V ≤ ∫ Re K(s x)(s x) dμ(x)`.
- `span_kernel_eq_top`: under `hint`, `V` is spanned by the functions `K(y)`, `y ∈ Y`
  (Waldspurger's `p_χ(°C_H) = F`).
- `kernel_apply_eq_sum` (Waldspurger's expansion of `α_χ`): for a finite index type `ι` and an
  orthonormal basis `b` of `hK.Space`, `K(y)(y') = Σ_i f_i(y') conj(f_i(y))` with
  `f_i = toSpace.symm (b i)`; with `K(y) = α_χ(·, y)` this is
  `α_χ(y', y) = Σ_i f_i(y') conj(f_i(y))`. It needs no integrability hypothesis; the
  existence of a finite orthonormal basis is an input.

## Proof notes

The implemented route differs from Waldspurger's, as in `ReproducingKernel`: no countable
basis or infinite sum is used.

1. The form `⟪f, g⟫ = B(g, f)` is sesquilinear by linearity of the integral (using
   `integrable`) and hermitian by `integral_conj`; `Re ⟪f, f⟫ = ∫ |f(s x)|² ≥ 0`.
2. Definiteness: `⟪K y, f⟫ = f(y)` by `reproduce`, so the Cauchy–Schwarz inequality for the
   pre-inner product (`InnerProductSpace.Core.inner_mul_inner_self_le`) gives
   `|f(y)|² ≤ Re ⟪K y, K y⟫ · Re ⟪f, f⟫`. If `⟪f, f⟫ = 0`, then `f(y) = 0` for every `y`, so
   `f = 0`. This makes `hK.Space` an inner product space (`InnerProductSpace.ofCore`).
3. Bessel's inequality (`Orthonormal.sum_inner_products_le`) for `toSpace (K y)` gives
   `Σ |e_i(y)|² ≤ ‖toSpace (K y)‖² = Re K(y)(y)`; applying it at `y = s x` and integrating,
   with `∫ |e_i(s x)|² = ‖toSpace (e i)‖² = 1`, gives `n ≤ ∫ Re K(s x)(s x)`.
4. A finite linearly independent family of `hK.Space` spans a finite-dimensional subspace
   with an orthonormal basis (`stdOrthonormalBasis`); by step 3 it has at most
   `⌊∫ Re K(s x)(s x) dμ⌋₊` elements, and `rank_le` bounds the rank. `V` is finite
   dimensional through the linear equivalence `toSpace`.
5. Spanning: in the finite-dimensional inner product space `hK.Space`, a vector `f`
   orthogonal to all `toSpace (K y)` has `f(y) = ⟪K y, f⟫ = 0`, so the orthogonal complement
   of the span of the kernel functions is zero (`Submodule.orthogonal_eq_bot_iff`).
6. Expansion: `toSpace (K y) = Σ_i ⟪b_i, toSpace (K y)⟫ b_i` (`OrthonormalBasis.sum_repr'`)
   and `⟪b_i, toSpace (K y)⟫ = conj ⟪toSpace (K y), b_i⟫ = conj(f_i(y))`; evaluate at `y'`.

## Relation to the Library

- `ReproducingKernel` (`IsReproducingKernel`) proves the same conclusions for a space of
  square-integrable functions on the measure space itself, through `L²(μ)`. It cannot be
  applied to `χ`-covariant functions on `G` with the quotient measure of `A_G\G`, as its
  Markdown records under "Open obligations": the functions are not functions on the
  quotient. The present module needs no `L²` space, no measurability of `f ∘ s` and no
  `mem` hypothesis on kernel functions (`K` takes values in `V` by its type), and its
  integrability hypothesis concerns only the products `f(s x) conj(g(s x))`.
- No other Library declaration provides this statement.

## Open obligations

The application to Waldspurger's `p_χ(°C_H)` is open. It needs: the quotient measure on
`A_G\G` and a section `s`; the identification of `∫ f₁(s x) conj(f₂(s x)) dμ(x)` with
Waldspurger's `(f₂, f₁)_{A_G\G}` (for unitary `χ` the integrand does not depend on the
section); the integrability of these products (the bound
`|f(g)| ≤ c Ξ(g)(1 + σ(g))^{-r}` on `G¹`, p. 328); formula (1) for `α_χ`, which uses
Lemma VIII.2.3 and the properties of `°e`; and the convergence of `∫_{A_G\G} α_χ(g, g) dg`
(Corollary VIII.3.2). None of these is proved here.
