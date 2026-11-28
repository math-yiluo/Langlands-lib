# Regular unitary elements at a place split in the quadratic extension

Module: `Langlands.Algebra.CentralSimple.UnitaryRegularSplit`, namespace
`Langlands.CentralSimple.UnitaryPoints`.

`F ⊆ E` is a separable quadratic extension with conjugation `e ↦ ē`
(`SU3Root.conjugation F E`), `B` a finite-dimensional central simple `E`-algebra that is an
`F`-algebra through `E`, and `τ : FirstKindInvolution F B` an involution with
`τ(e) = ē` on `E`. For a commutative `F`-algebra `K`, `τ_K = τ.baseChange K`.

## Coefficient maps (any commutative `F`-algebra `K`)

- `centerMap F E B K : K ⊗[F] E →ₐ[K] K ⊗[F] B` (abbrev), the map `ψ = id ⊗ (E → B)` of the
  statement; `centerMap_commute`: its image is central.
- `centerConj F E K : K ⊗[F] E →ₐ[K] K ⊗[F] E` (abbrev), `id ⊗ conj`; `centerConj_centerConj`.
- `baseChange_centerMap`: `τ_K ∘ ψ = ψ ∘ centerConj`; `baseChange_pow`; and
  `baseChange_eval₂`: `τ_K (f(x)) = (centerConj f)(τ_K x)` for `f` over `K ⊗[F] E` evaluated
  through `ψ` (expand `eval₂` as a finite sum; `τ_K` reverses products and `ψ` is central).

## The two components at a split place

Now `K` is a field and an `E`-algebra (`IsScalarTower F E K`), i.e. an `F`-embedding
`E → K` is fixed.

- `splitProj₁ F E K`, `splitProj₂ F E K : K ⊗[F] E →ₐ[K] K` (abbrevs): `k ⊗ e ↦ k e` and
  `k ⊗ e ↦ k ē`. They are exchanged by `centerConj` (`splitProj₁_centerConj`,
  `splitProj₂_centerConj`) and are jointly injective and surjective (`splitProj_injective`,
  `splitProj_surjective`), from the Library's `HermitianMatrix.tensorProj_bijective` after
  `Algebra.TensorProduct.comm`.
- The components of `K ⊗[F] B` are `q = tensorQuotient F E B K : K ⊗[F] B → K ⊗[E] B` and
  `y ↦ q(τ_K y)`, which is anti-multiplicative. On the image of `ψ` they are the scalars
  `splitProj₁` and `splitProj₂` (`tensorQuotient_centerMap`,
  `tensorQuotient_baseChange_centerMap`).
- `split_surjective`: for all `a, b ∈ K ⊗[E] B` there is `y` with `q y = a` and `q(τ_K y) = b`:
  take `ε` with projections `(1, 0)` and `y = ψ(ε) y₁ + τ_K(y₂) ψ(1 - ε)` with `q yᵢ` the
  prescribed values.
- `split_injective`: the pair is injective, because `K ⊗[F] B` and `(K ⊗[E] B)²` both have
  dimension `2 · finrank E B` over `K`.
- `tensorQuotient_eval₂`, `tensorQuotient_baseChange_eval₂`,
  `tensorQuotient_baseChange_centerMap_mul_pow`: the components of `f(y)` are
  `(f mapped by splitProj₁)(q y)` and `(f mapped by splitProj₂)(q(τ_K y))`.

## The main result

`exists_regular_unitary_of_split`: let `K` be a complete nontrivially normed field of
characteristic zero which is an `E`-algebra, `finrank E B = n²`, `z ∈ Eˣ`, and let `x₀` be a
unitary point of `K ⊗[F] B` (`x₀ ∈ unitaryPoints τ K`) with `relativeNorm x₀ = z ⊗ 1`. Then
the conclusion of `NumberFieldUnitaryRegularLocalStatement` holds with `K` in place of the
completion. The proof:

1. `A₁ = K ⊗[E] B` is central simple over `K` (`isSimpleRing_baseChange`,
   `isCentral_baseChange`) of reduced degree `n`. By `tensorProj_relativeNorm_eq_reducedNorm`
   and `reducedNorm_baseChange`, `a₀ = q x₀` has reduced norm `z` (via `E → K`).
2. `exists_norm_eq_with_separable_reducedCharpoly` gives `a ∈ A₁` of reduced norm `z` with
   separable reduced characteristic polynomial `g`; `a` is a unit
   (`isUnit_of_aeval_eq_zero`, `g(0) = (-1)ⁿ z`).
3. `mul_conjugation_eq_one` gives `z z̄ = 1`. Put `λ = (-1)ⁿ z̄` and `g₂ = λ · reverse g`; then
   `g₂` is separable (`separable_reverse`), `g₂(a⁻¹) = 0` (`aeval_inv_reflect_mul_pow`), and
   `g₂` is monic of degree `n`.
4. `x` is chosen with `q x = a` and `q(τ_K x) = a⁻¹` (`split_surjective`); both components of
   `x τ_K(x)` are `a a⁻¹ = 1`, so `x τ_K(x) = 1` (`split_injective`).
5. `f = C ε · g + C (1 - ε) · g₂` over `K ⊗[F] E` (the coefficients of `g`, `g₂` mapped by
   `algebraMap`) has components `g` and `g₂`. Monicity, degree and the coefficient relations
   `f_{n-i} = (-1)ⁿ (1 ⊗ z) conj(f_i)` are checked on the two projections, where they read
   `g_{n-i} = (-1)ⁿ z · λ g_{n-i}` and `λ g_i = (-1)ⁿ z̄ g_i`.
6. `f(x) = 0` and `f'(x)` is a unit componentwise: reduced Cayley–Hamilton,
   `isUnit_aeval_derivative_of_separable` for `g` at `a` and for `g₂` at `a⁻¹`, and an inverse
   assembled with `split_surjective`.
7. Independence of `1, x, …, x^{n-1}`: the components of `∑ ψ(cᵢ) xⁱ` are `∑ cᵢ⁽¹⁾ aⁱ` and
   `∑ cᵢ⁽²⁾ a⁻ⁱ`, which vanish only for `c⁽¹⁾ = c⁽²⁾ = 0`
   (`eq_zero_of_sum_smul_pow_eq_zero`, `eq_zero_of_sum_smul_inv_pow_eq_zero`).

## Provenance

Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.6, Step 1, printed
pp. 79–80 (PDF pp. 85–86), source `kneser-1969-galois-cohomology-classical-groups`: at a place
split in the quadratic extension the local algebra is a product of a central simple algebra and
its opposite, the first component of the local solution is replaced by a regular element of the
same reduced norm and the second is determined by unitarity. Platonov and Rapinchuk, *Algebraic
Groups and Number Theory* (1994), proof of Theorem 6.28, printed pp. 363–364 (PDF pp. 373–374),
source `platonov-rapinchuk-1994-algebraic-groups-number-theory`, relations (6.44). The Lean
proof works with the two components `q` and `q ∘ τ_K` instead of an explicit product
decomposition.
