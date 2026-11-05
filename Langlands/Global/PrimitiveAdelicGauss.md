# A rank-two height bound for actual primitive adelic vectors

This supporting module proves the rank-two height estimate behind the Gauss
(`GL₂`) step of the reduction of primitive adelic heights, for an arbitrary
number field `F` in universe `u`. All objects are the actual ones from
`Langlands.Global.PrimitiveAdelicHeight`: vectors in `Fin n → Adeles F` over
the full adele ring, maximum coordinate norms at every place, normalized finite
norms, and the archimedean multiplicities `w.mult` in the height.

## Provenance

The statement is derived. Springer, *Reduction theory over global fields*
(1994), §1.10, printed pp.210–211, PDF pp.4–5 (registered as
`springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`), proves
reduction for `GL₂` from the minimality inequality
`|t₁| ≤ ‖(λ + μ u) t₁ e₁ + μ t₂ e₂‖` for `λ, μ ∈ k` not both zero. Dividing by
`t₂` gives `|x| ≤ ‖(λ + μ u) x e₁ + μ e₂‖` with `x = t₁ / t₂`; his inequality
(3), `|x| ≤ ‖(u + v) x e₁ + e₂‖` for `v ∈ k`, is the case `μ = 1`. For
`k = ℚ` he chooses `v` to bound the right-hand side and deduces
`|x| ≤ 2/√3`. The vector `(λ + μ u) x e₁ + μ e₂` is
`rankTwoVector F x (u x) λ μ` here. This module bounds the height of such
vectors, for a suitable choice of coefficients, by `Cst √|x|` over an
arbitrary number field; combined with the minimality inequality this bounds
`|x|` by `Cst²`. That combination, and the minimality inequality itself, are
not proved in this module. With maximum norms over a
general number field the choice `μ = 1` with an integral correction does not
give such a bound, because the covering radius of the integer lattice in the
mixed space need not be small. This module therefore uses the project's
simultaneous Dirichlet approximation
`MixedSpaceDirichlet.exists_dirichlet_infiniteAdeles` with `N = ⌈√R⌉`, where
`R^d = |x|` and `d = [F : ℚ]`, together with a compact norm-one fundamental
set and a common integral denominator. The constant and the intermediate
lemmas are internal to this route and are not quoted from a single source
statement.

## Definition

* `rankTwoVector F x u l m`, for an idele `x`, an adele `u` and `l m : F`, is the
  actual adelic vector `![x * diagonal F l + u * diagonal F m, diagonal F m]` of
  `Vector F 2`.

## Results

* `rankTwoVector_eq_mulVec`: `rankTwoVector F x u l m` is the product of the
  adelic matrix `!![x, u; 0, 1]` with the rational vector `rational F 2 ![l, m]`.
* `norm_le_one_of_mem`: an element of the integers `v.adicCompletionIntegers F`
  of a finite completion has norm at most `1`.
* `finiteProjection_integer_mem`: the finite component at `v` of the principal
  adele of an algebraic integer lies in `v.adicCompletionIntegers F`.
* `exists_denominator_of_isCompact`: every compact set of finite adeles has a
  nonzero algebraic integer `d` such that `d * a v` is integral at every finite
  place `v` for every element `a` of the set.
* `exists_infinite_bound_of_isCompact`: for a compact set of ideles there is a
  real `A ≥ 0` bounding the norm of every infinite component of every element.
* `height_le_pow_of_local_le`: if a vector of `Vector F n` has finite norm at
  most `1` at every finite place and infinite norm at most `M ≥ 0` at every
  infinite place, then its height is at most `M ^ [F : ℚ]`.
* `norm_first_eq_one`, `height_rational_first`: the vector `![1, 0]` has
  maximum norm `1` in any normed field, and the rational vector
  `rational F 2 ![1, 0]` has height `1`.
* `height_rankTwoVector_one_zero`: with coefficients `(1, 0)` the height of
  `rankTwoVector F x u 1 0` equals the normalized idele absolute value
  `IdeleAbsoluteValue.full F x`.
* `exists_rankTwoVector_height_le` (main result): there is a constant
  `Cst > 0` such that for every idele `x` and every adele `u` there are
  `l m : F`, not both zero, with
  `height F 2 (rankTwoVector F x u l m) ≤ Cst * √|x|`, where `|x|` is
  `IdeleAbsoluteValue.full F x` as a real number. The constant depends only on
  `F`.

## Proof

`exists_denominator_of_isCompact` covers the compact set by the open sets of
finite adeles `a` with `d * a` in the integral finite adeles, `d` ranging over
the nonzero algebraic integers (every finite adele has such a denominator by
`exists_integer_mul_mem_adicCompletionIntegers`). A finite subcover gives the
product of finitely many denominators. `exists_infinite_bound_of_isCompact`
bounds the continuous sum of the infinite component norms on the compact set.
`height_le_pow_of_local_le` bounds the infinite product using
`∑ w, w.mult = [F : ℚ]`; the finite product is at most `1`, both when the
multiplicative support is finite and, by the convention of `finprod`, when it
is infinite. `height_rankTwoVector_one_zero` writes the vector as `x` times the
primitive rational vector `(1, 0)` and applies the published scaling law
`IsPrimitive.height_smul`.

For the main result, fix a compact set `C` of norm-one ideles with
`NormOneIdeleClass.exists_isCompact_fundamentalSet`, a bound `A` for the
infinite components of `C`, a common denominator `D` for the finite components
of `C`, the bound `E` given by the sum of the infinite norms of `D`, and
`B = MixedSpaceDirichlet.basisBound F`. Put `K = E * B * (A + 2)` and
`Cst = max (K^d) 1`.

* If `|x| ≤ 1`, take `(l, m) = (1, 0)`; the height is `|x| ≤ √|x|`.
* Otherwise let `r = scalarRoot F |x|`, so `R = r ≥ 1` and `R^d = |x|`, and let
  `s = PositiveRealIdeles.full F r`, which has absolute value `|x|`. Then
  `s⁻¹ x` has norm one, so some principal unit `a` gives
  `c = a (s⁻¹ x) ∈ C`. With `t = s c` one has `x * diagonal a = t`. Write
  `u = z t` and choose `q ∈ F` with `z - q` integral at every finite place
  (`exists_sub_mem_integralFiniteAdeles`); let `y = z - q`. Apply the Dirichlet
  theorem to the infinite part of `y` with `N = ⌈√R⌉`, obtaining algebraic
  integers `l₀` and `m₀ ≠ 0`. The coefficients are
  `l = a D (l₀ - m₀ q)` and `m = D m₀`, so `m ≠ 0`, and the vector is
  `![t * (D (l₀ + m₀ y)), D m₀]`.
* At a finite place `t` has the same component as `c` (the finite components
  of `s` are `1`), `D c` is integral and `y`, `l₀`, `m₀`, `D` are integral, so
  both coordinates have norm at most `1`.
* At an infinite place `w`, the component of `s` has norm `R`, so the first
  coordinate has norm at most `R A E B / N ≤ A E B √R`, using `R / N ≤ √R`. The
  second has norm at most `E N B ≤ 2 E B √R`, using `N ≤ 2 √R`. Both are at
  most `K √R`.
* Hence the height is at most `(K √R)^d = K^d √|x| ≤ Cst √|x|`, since
  `(√R)^d = √(R^d)`.

## Scope

Only the rank-two estimate for the vector `rankTwoVector F x u l m` is proved.
The Iwasawa decomposition of actual adelic general linear groups, the
comparison of heights under compact factors, the resulting `GL₂` reduction,
the higher-rank induction, the descent to connected reductive groups and the
general reductive Siegel-cover theorem are not asserted here.
