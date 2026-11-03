# Reproducing kernels and finite dimensionality (Waldspurger VIII.4.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ReproducingKernel`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published module
`CentralProjection` (for `centralProjection`, `centralProjection_mul_left` and
`IsBiInvariant.centralProjection`) and Mathlib's `L²` space and Euclidean spaces.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Proposition VIII.4.1, printed p. 327 (PDF p. 93): for every compact open subgroup `H` and
  every `χ ∈ Â_G`, the space `p_χ(°C_H)` is finite dimensional.
- Its proof, printed pp. 328–330 (PDF pp. 94–96):
  - "One may assume that the restriction of `χ` to `A_G ∩ H` is trivial, otherwise
    `p_χ(°C_H) = {0}`."
  - On `p_χ(°C_H)` the positive definite hermitian product is
    `(f₁, f₂)_{A_G\G} = ∫_{A_G\G} conj(f₁(g)) f₂(g) dg`.
  - The kernel `α_χ` satisfies `α_χ(·, g) ∈ p_χ(°C_H)` and formula (1):
    `(α_χ(·, g), f)_{A_G\G} = f(g)` for `f ∈ p_χ(°C_H)` and `g ∈ G`.
  - With `F` the span of the `α_χ(·, g)` and a countable orthonormal basis `(f_i)_{i∈I}`
    of `F`, (1) gives `α_χ(g₁, g₂) = ∑_i f_i(g₁) conj(f_i(g₂))`. Hence
    `∫_{A_G\G} α_χ(g, g) dg` converges if and only if `I` is finite. Its convergence makes
    `F` finite dimensional. By (1) the orthogonal complement of `F` in `p_χ(°C_H)` is
    zero, so `p_χ(°C_H) = F`.
  - The convergence is Corollary VIII.3.2, printed p. 326 (proof p. 327). The text on
    p. 330 prints "Corollaire III.3.2", a misprint: Lemma III.3.2 (printed pp. 267–268) is
    a lemma about weak constant terms. The published source map
    `notes/plancherel/waldspurger-source-map.md` records the same correction.

## Scope: abstract data and explicit hypotheses

The kernel part works over an arbitrary measurable space `X` with an arbitrary measure
`μ`, a submodule `V` of the complex functions `X → ℂ` and a function `K : X → X → ℂ`. The
pairing is the `L²(μ)` product `(f₁, f₂) = ∫ conj(f₁) f₂ dμ`, which agrees with
Waldspurger's convention. The structure `IsReproducingKernel μ V K` bundles three
hypotheses:

- `memLp`: every `f ∈ V` is in `L²(μ)`;
- `mem`: every function `K(·, x) = fun y => K y x` lies in `V`;
- `reproduce`: `∫ f(y) conj(K(y, x)) dμ(y) = f(x)` for every `f ∈ V` and every `x ∈ X`,
  i.e. `(K(·, x), f) = f(x)` (Waldspurger's formula (1)).

The finiteness results take the further hypothesis `hint`: `x ↦ Re K(x, x)` is
`μ`-integrable (Waldspurger's convergence of `∫ α_χ(g, g) dg`).

Mathlib's `RKHS` class is not used. It starts from an inner product space with a
continuous injective linear map to functions, and its kernel functions `RKHS.kerFun` are
adjoints, which need the space to be complete. Here `V` is a priori not complete for the
pairing, and the pairing is not an instance on `V`. Completeness follows from the finite
dimensionality proved here.

The character part works over a group `G`, a subgroup `A` and a homomorphism
`χ : A →* ℂˣ`. Its hypotheses are listed with the results.

## Definitions

- `IsReproducingKernel μ V K`, the structure above.
- `IsReproducingKernel.kernel hK x : V`, the function `K(·, x)` as an element of `V`.
- `IsReproducingKernel.embed hK : V →ₗ[ℂ] Lp ℂ 2 μ`, the class of `f ∈ V` in `L²(μ)`.

## Results

All results in the namespace `IsReproducingKernel` assume `hK : IsReproducingKernel μ V K`.

- `coeFn_embed`: `embed f` agrees with `f` `μ`-almost everywhere.
- `inner_embed`: `⟪embed f, embed g⟫ = ∫ conj(f(y)) g(y) dμ(y)`.
- `inner_embed_kernel`: `⟪embed (kernel x), embed f⟫ = f(x)`, the reproducing property in
  `L²(μ)`.
- `embed_injective`: `embed` is injective. A function of `V` that vanishes in `L²(μ)`
  vanishes at every point, by `inner_embed_kernel`.
- `norm_sq_embed`: `‖embed f‖² = ∫ |f(y)|² dμ(y)`.
- `kernel_diag`: `K(x, x) = ‖embed (kernel x)‖²`, so `K(x, x)` is real and nonnegative.
  Also `kernel_diag_eq_integral` (`K(x, x) = ∫ |K(y, x)|² dμ(y)`), `re_kernel_diag` and
  `re_kernel_diag_nonneg`.
- `sum_norm_sq_le` (Bessel's inequality at a point): for a finset `s` of indices and
  `v : ι → V` whose image under `embed` is orthonormal (hypothesis `hv`),
  `∑_{i ∈ s} |v_i(x)|² ≤ Re K(x, x)` for every `x`.
- `card_le_of_orthonormal`: under `hint`, every `v : Fin n → V` with orthonormal image
  under `embed` has `n ≤ ∫ Re K(x, x) dμ`.
- `finrank_le_of_le_range`: under `hint`, every finite-dimensional submodule `E` of
  `L²(μ)` contained in the range of `embed` (hypothesis `hE`) has
  `dim E ≤ ∫ Re K(x, x) dμ`.
- `finiteDimensional` (finite dimensionality, Proposition VIII.4.1 in abstract form):
  under `hint`, `V` is finite dimensional.
- `finrank_le`: under `hint`, `dim V ≤ ∫ Re K(x, x) dμ`.
- `span_kernel_eq_top`: under `hint`, `V` is spanned by the functions `K(·, x)`, `x ∈ X`
  (Waldspurger's `p_χ(°C_H) = F`).
- `kernel_eq_sum` (Waldspurger's expansion of `α_χ`): for a finite index type `ι`, an
  orthonormal basis `b` of the range of `embed` and `v : ι → V` with `embed (v i) = b i`
  (hypothesis `hv`), `K(y, x) = ∑_i v_i(y) conj(v_i(x))` for all `x, y`. It needs no
  integrability hypothesis; the existence of a finite orthonormal basis is an input.

For the first reduction in the proof, `G` is a group, `A` a subgroup and
`χ : A →* ℂˣ` a homomorphism:

- `eq_zero_of_covariant`: if `A ≤ Z(G)` (hypothesis `hA`), `f : G → ℂ` satisfies
  `f(a g) = χ(a) f(g)` for all `a ∈ A`, `g ∈ G` (hypothesis `hcov`) and
  `f(g h) = f(g)` for all `h ∈ H`, `g ∈ G` (hypothesis `hH`), and some `a ∈ A` lies in `H`
  (hypothesis `ha`) with `χ(a) ≠ 1` (hypothesis `hχ`), then `f = 0`.
- `centralProjection_eq_zero_of_ne_one`: let `A` carry a measurable structure with
  measurable multiplication and a right-invariant measure `μ_A`. Assume `hA`, that `f` is
  bi-invariant under `H` (hypothesis `hf`), `ha` and `hχ`. Then `p_χ f = 0`. Hence
  `p_χ(°C_H) = {0}` when `χ` is nontrivial on `A ∩ H`. No integrability or unitarity is
  assumed: `centralProjection` is a Bochner integral, and the covariance
  `centralProjection_mul_left` holds for every `f`.

## Proof notes

The implemented route differs from Waldspurger's. He takes a countable orthonormal basis
of the span `F` of the kernel functions, expands `α_χ` in it and compares
`∫ α_χ(g, g) dg` with the number of basis vectors. Here no countable basis or infinite
sum is used. Instead:

1. Bessel's inequality (`Orthonormal.sum_inner_products_le` in `L²(μ)`), applied to
   `embed (kernel x)` and a finite orthonormal family `embed ∘ v`, gives
   `∑ |v_i(x)|² ≤ ‖embed (kernel x)‖² = Re K(x, x)`, since `⟪embed (v i), embed (kernel x)⟫`
   has absolute value `|v_i(x)|` by the reproducing property.
2. Integrating over `X` with `∫ |v_i|² = ‖embed (v i)‖² = 1` gives
   `n ≤ ∫ Re K(x, x) dμ`.
3. A finite linearly independent family in `V` maps injectively to `L²(μ)`. Its span
   there is finite dimensional and has an orthonormal basis (`stdOrthonormalBasis`), which
   lifts to `V` along `embed`. So every such family has at most `⌊∫ Re K(x, x) dμ⌋₊`
   elements, and `rank_le` bounds the rank of `V`.
4. Spanning: `V` is finite dimensional, so the image `P` of the span of the kernel
   functions is a finite-dimensional, hence complete, subspace of `L²(μ)`. Decompose
   `embed f = embed g' + z` with `g'` in the span and `z ⊥ P`
   (`exists_add_mem_mem_orthogonal`). Then `z = embed (f - g')`, and `(f - g')(x)` is the
   inner product of `embed (kernel x) ∈ P` with `z`, which is `0`. So `f = g'`.
5. Expansion: Parseval's identity `∑_i ⟪u, b_i⟫ ⟪b_i, w⟫ = ⟪u, w⟫`
   (`OrthonormalBasis.sum_inner_mul_inner`) for `u = embed (kernel y)` and
   `w = embed (kernel x)`, with `⟪embed (kernel y), embed (kernel x)⟫ = K(y, x)` and
   `⟪embed (kernel y), b_i⟫ = v_i(y)`.

The first reduction: for central `a ∈ A ∩ H`, `f(g) = f(g a) = f(a g) = χ(a) f(g)`, so
`f(g) = 0` when `χ(a) ≠ 1`. It applies to `p_χ f`, which is `χ`-covariant
(`centralProjection_mul_left`) and bi-invariant under `H` (`IsBiInvariant.centralProjection`).

## Open obligations

Applying these results to Waldspurger's `p_χ(°C_H)` is open. It needs a measure `μ` on a
space of points carrying the functions of `p_χ(°C_H)`, such that `∫ F dμ` equals the
quotient integral `∫_{A_G\G} F(g) dg` for the `A_G`-invariant integrands
`conj(f₁) f₂` that occur. The restriction of the Haar measure of `G` to a measurable
transversal of the cosets `A_G g` does not work: when `G = A_G` (for instance
`G = GL₁(ℚ_p)`) a transversal is a single point, of Haar measure zero, while the
normalized quotient measure of the one-point quotient is one; with the zero measure
`reproduce` forces `V = 0`. One candidate is the image on `G` of the quotient measure of
`A_G\G` along a measurable section; it is not in general a restriction of Haar measure. Its
construction, its normalization and the comparison of its pairing with Waldspurger's
`(·,·)_{A_G\G}` are open. The application also needs the verification of `memLp`, `mem`
and `reproduce` for `α_χ` (formula (1), which uses Lemma VIII.2.3 and the properties of
`°e`) and the convergence of `∫_{A_G\G} α_χ(g, g) dg` (Corollary VIII.3.2, printed p. 326;
misprinted as III.3.2 on p. 330). None of these is proved here.
