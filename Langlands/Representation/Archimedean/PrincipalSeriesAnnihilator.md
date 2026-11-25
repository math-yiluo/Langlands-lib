# Orthogonal vectors for proper `O(n)`-stable subspaces of principal series

Lean module: `Langlands.Representation.Archimedean.PrincipalSeriesAnnihilator`.

Let `W` be an `O(n)`-stable subspace of the `O(n)`-finite functions of a real principal series of
`GL_n(ℝ)`, and suppose `W` is not all of that space. This module finds an `O(n)`-finite function
`v` of the same principal series, not identically zero on `O(n)`, that is orthogonal to `W` in
`L²(O(n))`. The statement is `Langlands.Archimedean.PrincipalSeriesOrthogonalVectorStatement`,
proved as `Langlands.Archimedean.principalSeriesOrthogonalVector`.

For the proof of the Langlands-quotient statement `RealStandardLanglandsQuotientStatement`,
`v` produces a nonzero vector of the dual principal series that annihilates `W` in
the `O(n)`-integral pairing: the complex conjugate of `v` on `O(n)` is extended to the dual
principal series with the module `PrincipalSeriesExtension`. This module does
not depend on it.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ` and `O(n)` is the subgroup
`unitaryCompact ℝ n`. `principalSeries ℝ n χ`, `kFiniteFunctions` and `Whittaker.rightTranslation`
(`(R(k) f)(x) = f(x k)`) are the Library's. `RealPrincipalSeriesDuality.haarK n` is the Library's
normalized Haar measure on `O(n)` (`RealPrincipalSeriesDualityProof`), with its Borel
σ-algebra `measurableSpaceK`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.PrincipalSeriesAnnihilator`.

## The statement

`PrincipalSeriesOrthogonalVectorStatement`: let `n` be a natural number, `χ : ℕ → ℝˣ → ℂ` any
characters, `W` a submodule of the functions on `GL_n(ℝ)`, and `f` a function on `GL_n(ℝ)`, with

* `W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)`;
* `R(k) w ∈ W` for every `k ∈ O(n)` and `w ∈ W`;
* `f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)` and `f ∉ W`.

Then there is `v ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)` with `v(k) ≠ 0` for
some `k ∈ O(n)`, and `∫_{O(n)} w(k) · conj(v(k)) d(haarK n)(k) = 0` for every `w ∈ W`.

No condition on the characters `χ` is needed. Only stability under `O(n)` is assumed, not under the
Lie algebra.

Provenance. Derived, internal infrastructure without a literature source. The underlying facts are
standard for admissible representations of compact groups: finite-dimensional unitary
representations are completely reducible, and the multiplicity of every finite-dimensional
representation in a principal series is finite (Frobenius reciprocity). The proof below is
self-contained.

## Definitions

Abstract part (section `Abstract`): `E` is a complex inner product space, `G` a group and
`ρ : Representation ℂ G E`.

* `IsStable ρ F`: the submodule `F` is mapped into itself by every `ρ(g)`.
* `equivariantMaps ρ F hF`: the `G`-equivariant linear maps from a stable submodule `F` to `E`, as a
  submodule of `F →ₗ[ℂ] E`.

Concrete part (section `Concrete`):

* `KFin n χ`: the `O(n)`-finite functions of the principal series of `χ`, as a type synonym of the
  submodule. It carries the `L²(O(n))` inner product
  `⟪x, y⟫ = ∫_{O(n)} conj(x(k)) y(k) d(haarK n)(k)` (`l2Inner`; instances `InnerProductSpace.Core`,
  `NormedAddCommGroup`, `InnerProductSpace` built with Mathlib's `InnerProductSpace.ofCore`).
  `KFin.toFun` is the underlying function on `GL_n(ℝ)`, `KFin.mk` builds an element, and
  `KFin.toFunLinear` is `toFun` as a linear map.
* `rho`: right translation by `O(n)` on `KFin n χ`.

## Proof

1. **Abstract theorem** (`exists_ne_zero_inner_eq_zero`). Assume `ρ` preserves the inner product,
   every vector generates a finite-dimensional stable subspace, and for every finite-dimensional
   stable `F` the space `equivariantMaps ρ F hF` is finite-dimensional. Then a stable submodule `W`
   with some `f ∉ W` has an orthogonal vector `v ≠ 0`. Proof:
   * `F` is the span of the orbit of `f`, and `Y` is the sum of the images of a basis `bᵢ` of
     `equivariantMaps ρ F hF`. `Y` is finite-dimensional and stable, every equivariant map `F → E`
     takes values in `Y`, and `f ∈ Y` (inclusion of `F`).
   * The orthogonal projection `P = Y.starProjection` commutes with `ρ`
     (`starProjection_equivariant`, via `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`).
   * `P` maps `W` into `W`. For `w ∈ W`, let `Z` be the span of its orbit (`Z ≤ W`),
     `N = Z ⊓ ker P` and `Z' = Nᗮ ⊓ Z`, so that `Z = N ⊔ Z'`
     (`Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`). `P` is injective on `Z'`; let `R`
     be its image and `e : Z' ≃ R`. Then `S = e⁻¹ ∘ (projection onto R)` is equivariant, so `S ∘ bᵢ`
     is an equivariant map `F → E` and `S` maps `Y` into `Y`. Since `S(P z) = z` for `z ∈ Z'`, this
     gives `Z' ≤ Y`. Writing `w = a + c` with `a ∈ N`, `c ∈ Z'`, we get `P w = c ∈ Z ≤ W`.
   * Let `V₀ = Y ⊓ W`. Since `f ∈ Y ∖ V₀`, the space `V₀ᗮ ⊓ Y` is nonzero; take `v ≠ 0` in it. For
     `w ∈ W`, `⟪v, w⟫ = ⟪v, P w⟫ + ⟪v, w − P w⟫ = 0`, because `P w ∈ V₀` and `w − P w ∈ Yᗮ`.
2. **The inner product.** `⟪x, x⟫ = ∫ ‖x(k)‖² dk` (`l2Inner_self`, from `RCLike.conj_mul`). It
   vanishes only if the continuous function `‖x(k)‖²` vanishes almost everywhere, hence everywhere
   (Haar measure is positive on open sets). Then `x = 0`, because a principal-series function
   vanishing on `O(n)` is zero (Library `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`).
3. **Hypotheses of step 1 for `KFin`.** `rho` preserves the inner product by right invariance of
   `haarK n` (`rho_isometry`, `integral_mul_right_eq_self`). Orbits are finite-dimensional because
   the functions are `O(n)`-finite (`finiteDimensional_orbit`). Finite multiplicities
   (`finiteDimensional_equivariantMaps`): evaluation at `1`, `T ↦ (x ↦ (T x)(1))`, is injective on
   equivariant maps, since `(T x)(k) = (R(k)(T x))(1) = (T(R(k) x))(1)` determines `T x` on `O(n)`.
4. **Conclusion** (`exists_orthogonal`). Apply step 1 to `W' = {x : KFin n χ | x.toFun ∈ W}` and
   `KFin.mk f`. The resulting `v` is nonzero on `O(n)` by step 2, and
   `∫ w(k) conj(v(k)) dk = ⟪v, w⟫ = 0` for `w ∈ W`.
