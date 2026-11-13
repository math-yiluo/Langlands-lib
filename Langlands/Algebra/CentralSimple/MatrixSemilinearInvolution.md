# Semilinear involutions descend from matrix algebras to division rings

Author: Worker 166.

This module proves that an involution of the second kind on a matrix algebra
`Matrix ι ι D` over a division ring `D` gives an involution of the second kind on `D`
itself, for the same automorphism of the base field. It is the pure-algebra corner step
of the general-field implication `UnitaryDivisionCommutative K →
UnitaryInvolutionSplitting K` (Worker 150's statement module
`Langlands/Algebra/UnitaryInvolutionStatements`). That implication is part of Task 5973.
This module does not prove it: Wedderburn–Artin and the dimension count `finrank L D = 1`
are not used here.

Throughout, `L` is a field, `σ : L →+* L` is a ring endomorphism, and "nontrivial" means
the hypothesis `hσ : ∃ ω, σ ω ≠ ω`. For an `L`-algebra `A`, a map `τ : A → A` is a
*`σ`-semilinear involution* when it satisfies the four conditions

- `τ (x + y) = τ x + τ y` (additive),
- `τ (x * y) = τ y * τ x` (anti-multiplicative),
- `τ (τ x) = x` (involutive),
- `τ (algebraMap L A c) = algebraMap L A (σ c)` (restricts to `σ` on `L`).

These are the four conjuncts of `Langlands.IsUnitaryInvolution σ τ` in Worker 150's
statement module. This module states them separately so that it depends only on
Mathlib.

## Definitions

- `rowMulLinear X`: for `X : Matrix ι ι D` with `ι` finite, the map `v ↦ v ᵥ* X` (row
  vector times matrix) as a `D`-linear endomorphism `(ι → D) →ₗ[D] (ι → D)` of the
  left `D`-module of row vectors. `rowMulLinear_apply` is its defining equation. It is
  used to measure the "rank" of an idempotent matrix over a noncommutative division ring.

## Statements

- `exists_involution_of_sq_eq_conj` (twist lemma). Let `D` be a division `L`-algebra
  and let `σ` be nontrivial. Let `θ₀ : D → D` be additive, anti-multiplicative, with
  `θ₀ (algebraMap L D c) = algebraMap L D (σ c)`. Suppose there is `a ≠ 0` in `D` with
  `θ₀ (θ₀ x) = a * x * a⁻¹` for all `x` and `θ₀ a = a⁻¹`. Then `D` has a
  `σ`-semilinear involution.
- `exists_mul_eq_single_of_antiHom` (Murray–von Neumann equivalence). Let `ι` be finite
  with decidable equality, `D` a division ring, and `τ` an additive, anti-multiplicative
  map of `Matrix ι ι D` with `τ 1 = 1`. For every `i₀` there are matrices `y`, `z` with
  `z * y = single i₀ i₀ 1` and `y * z = τ (single i₀ i₀ 1)`.
- `exists_semilinear_involution_of_matrix` (corner). For `ι` finite and nonempty, a
  `σ`-semilinear involution of `Matrix ι ι D`, with `σ` nontrivial, gives a
  `σ`-semilinear involution of `D`. Here `L` acts on matrices through the scalar
  matrices `algebraMap L (Matrix ι ι D)`.
- `exists_semilinear_involution_of_algEquiv_matrix` (main result). Let `B` be an
  `L`-algebra (any ring), `D` a division `L`-algebra, `ι` finite and nonempty, and
  `Φ : B ≃ₐ[L] Matrix ι ι D`. If `σ` is nontrivial and `B` has a `σ`-semilinear
  involution, then `D` has a `σ`-semilinear involution.

No finiteness, centrality or simplicity hypothesis on `D` or `B` is needed, and `σ` is
only assumed to be a nontrivial ring endomorphism. The proofs show `σ (σ c) = c` from the
hypotheses.

## Proofs

**Twist lemma.** First `θ₀ 1 = 1` (the case `c = 1`), so `θ₀ x⁻¹ = (θ₀ x)⁻¹` for
`x ≠ 0`. Also `σ (σ c) = c`: both sides map to `a * c * a⁻¹ = c` in `D`, because scalars
are central, and `algebraMap L D` is injective. Then `θ₀ a⁻¹ = a`. Put
`φ x = a⁻¹ * θ₀ x`. Then `φ` is additive, `φ (c * x) = σ c * φ x` for scalars `c`, and
`φ (φ x) = a⁻¹ * θ₀ (θ₀ x) * θ₀ a⁻¹ = a⁻¹ * (a * x * a⁻¹) * a = x`.
So `φ` is a `σ`-semilinear additive involution, and it has a nonzero fixed vector `b`:
take `b = 1 + φ 1` if this is nonzero. Otherwise `φ 1 = -1`; then take
`b = ω + σ ω * φ 1 = ω - σ ω`, which is nonzero since `σ ω ≠ ω` and is fixed by `φ`.
From `φ b = b` we get `θ₀ b = a * b`, hence `θ₀ b⁻¹ = b⁻¹ * a⁻¹`. The required map is
`θ x = b * θ₀ x * b⁻¹`. It is additive and anti-multiplicative, and it restricts to `σ`
on scalars. It is involutive because
`θ (θ x) = b * (b⁻¹ * a⁻¹) * (a * x * a⁻¹) * (a * b) * b⁻¹ = x`.

**Murray–von Neumann equivalence.** Put `F i j = τ (single j i 1)`. Since `τ` reverses
products, these matrices multiply like matrix units: `F i j * F k l` is `F i l` if
`j = k` and `0` otherwise, and `∑ i, F i i = τ 1 = 1`. Let `F₀ = F i₀ i₀`, an idempotent,
and let `W` be the range of `rowMulLinear F₀`, the row vectors `v` with `v ᵥ* F₀ = v`.
The maps `v ↦ (v ᵥ* F i i₀)ᵢ` from `ι → D` to `ι → W` and `(wᵢ) ↦ ∑ i, wᵢ ᵥ* F i₀ i` back
are mutually inverse `D`-linear maps. So `card ι = card ι * finrank D W`, and therefore
`finrank D W = 1`. Choose a nonzero `u` spanning `W`. Every row `Pi.single j 1 ᵥ* F₀` of
`F₀` is a multiple `c j • u`. So `F₀ j k = c j * u k`, and `u ᵥ* F₀ = u` gives
`∑ j, u j * c j = 1`. The matrices `y` with column `i₀` equal to `c` (other columns
zero) and `z` with row `i₀` equal to `u` (other rows zero) satisfy
`z * y = single i₀ i₀ 1` and `y * z = F₀`.

**Corner.** Let `e = single i₀ i₀ 1` and `f = τ e`. Then `e` and `f` are idempotents
and `τ f = e`. From the previous step, after replacing `z` by `z * f` and `y` by
`y * e`, we have `e z = z = z f`, `f y = y = y e`, `z y = e` and `y z = f`. The corner
`e * Matrix * e` is identified with `D` by `d ↦ single i₀ i₀ d`. Define
`θ₀ d = (z * τ (single i₀ i₀ d) * y) i₀ i₀`. Every `z * X * y` lies in the corner, so
it equals `single i₀ i₀` of its `(i₀, i₀)` entry. Hence `θ₀` is additive, and it is
anti-multiplicative because `τ` of a corner element `X` satisfies `f * τ X = τ X`, so
`z * τ (X₁ * X₂) * y = (z * τ X₂ * y) * (z * τ X₁ * y)` after inserting `y * z = f`. It restricts to `σ` on scalars because `z * f * y = z * y = e`.
Put `a = (z * τ y) i₀ i₀` and `a' = (τ z * y) i₀ i₀`. Both `z * τ y` and `τ z * y` lie
in the corner, and `(z * τ y) * (τ z * y) = z * τ (z * y) * y = z * f * y = e`, so
`a * a' = 1` and `a' = a⁻¹`. Expanding with `τ (τ X) = X` gives
`θ₀ (θ₀ d) = a * d * a⁻¹` and `θ₀ a = a⁻¹`. The twist lemma then gives the involution
on `D`.

**Main result.** Transport `τ` along `Φ` to `X ↦ Φ (τ (Φ.symm X))` on
`Matrix ι ι D`. It is again a `σ`-semilinear involution, since `Φ` is an `L`-algebra
isomorphism. Then apply the corner theorem.

## Provenance

Internal; derived. The mathematical fact is classical. It is the case
`A = Mr(D)` of the remark following Theorem (3.1)(2) in Knus, Merkurjev, Rost and
Tignol, *The Book of Involutions* (1998), printed p.31 (PDF p.54): "if a central simple
algebra has an involution, then every Brauer-equivalent algebra has an involution of the
same kind". The book deduces that remark from the Albert–Riehm–Scharlau criterion via
the norm algebra. This module instead proves the special case directly, by the
elementary corner argument (`e B e ≅ D`, with `τ(e)` equivalent to `e`, followed by a
twist by an inner automorphism) that Worker 150 outlined for Task 5973. Its hypotheses
are weaker than the book's: no finite-dimensionality or centrality is assumed, and `σ`
need only be a nontrivial ring endomorphism of `L`. The Lean statements are internal
formulations; no external statement is transcribed.
