# Normal-basis filtrations of the units of a complete ultrametric field

Author: Worker 226.

This module produces, for a finite Galois extension `L/K` with `L` a complete ultrametric
normed field, a `Gal(L/K)`-stable subgroup `V` of `Lˣ`. Every multiplicative `1`- and
`2`-cocycle of `Gal(L/K)` with values in `V` is a coboundary of a cochain with values in
`V`. The subgroup `V` contains all units `u` with `‖u - 1‖` small. Only the norm on `L` is
used; `K` carries no norm.

## The data

`LatticeData K L` (for `[Field K] [NormedField L] [Algebra K L]`) bundles:

- `basis : Module.Basis (L ≃ₐ[K] L) K L` with `basis σ = σ (basis 1)` (a normal basis) and
  `‖basis σ‖ ≤ 1`;
- `norm_map`: every `σ : L ≃ₐ[K] L` preserves the norm;
- `ϖ : K` with `0 < ‖algebraMap K L ϖ‖ < 1`; `radius` is this norm `r`;
- `c : ℕ` with `norm_coord_le`: if `‖x‖ ≤ r ^ c` then every coordinate of `x` in `basis`
  has norm (in `L`) at most `1`.

Write `M` for the elements whose coordinates all have norm at most `1`, i.e. the lattice
spanned by the normal basis over the `ϖ`-integral elements of `K`. The last field says
`ϖ^c O_L ⊆ M`. The module never forms `M` as a separate object; it works with the
coordinate functions `coord x σ = algebraMap K L (basis.repr x σ)`.

## Coordinates

- `coord_add`, `coord_sub`, `coord_neg`, `coord_algebraMap_mul`: the coordinates are
  `K`-linear.
- `repr_map` and `coord_map`: `basis.repr (τ x) σ = basis.repr x (τ⁻¹ * σ)`. Since
  `τ (basis ρ) = basis (τ * ρ)`, the two `K`-linear maps agree on the basis.
- `repr_sum`: the coordinates of `∑ ρ, k ρ • basis ρ` are `k`.
- `norm_le_of_coord`: if all coordinates of `x` have norm at most `s ≥ 0`, then
  `‖x‖ ≤ s`. This uses the ultrametric inequality and `‖basis σ‖ ≤ 1`.
- `norm_coord_le_pow`: if `‖x‖ ≤ r ^ (c + j)`, every coordinate of `x` has norm at most
  `r ^ j`. Apply `norm_coord_le` to `ϖ^{-j} x`.

## The filtration

`IsNear m u` means `u ≡ 1 mod ϖ^m M`: every coordinate of `u - 1` has norm at most `r ^ m`.

- It implies `‖u - 1‖ ≤ r ^ m` (`IsNear.norm_sub_one_le`) and, for `m > 0`, `‖u‖ = 1`
  (`IsNear.norm_eq_one`).
- It follows from `‖u - 1‖ ≤ r ^ (c + m)` (`isNear_of_norm_sub_one_le`).
- It is monotone in `m` (`IsNear.mono`) and preserved by `Gal(L/K)` (`IsNear.map`).
- For `m > c` it is preserved by products and inverses (`IsNear.mul`, `IsNear.inv`,
  `IsNear.div`). The key estimate `norm_coord_mul_le` says that if `‖x‖, ‖y‖ ≤ r ^ m` and
  `m > c`, then the coordinates of `x * y` have norm at most `r ^ (m + 1)`, because
  `2m ≥ c + (m + 1)`. The proofs use
  `u u' - 1 = (u - 1) + (u' - 1) + (u - 1)(u' - 1)` and
  `u⁻¹ - 1 = -(u - 1) + (u - 1)((u - 1) u⁻¹)`.

`filtration m hm` (for `hm : c < m`) is the resulting subgroup `V_m` of `Lˣ`. The canonical
filtration is `unitFiltration k = V_{c+1+k}`. It is `Gal(L/K)`-stable
(`smul_mem_unitFiltration`) and consists of norm-one units
(`norm_eq_one_of_mem_unitFiltration`). Its level `0` contains every unit with
`‖u - 1‖ ≤ r ^ (c + (c + 1))` (`mem_unitFiltration_zero_of_norm_le`). It is separated
(`eq_one_of_forall_mem_unitFiltration`). Under `[CompleteSpace L]` it is complete
(`exists_prod_unitFiltration`). There, the partial products `Q k` of a sequence
`b k ∈ V_{c+1+k}` satisfy `dist (Q k) (Q (k+1)) ≤ r^{c+1} r^k`, so they are Cauchy
(`cauchySeq_of_le_geometric`) and converge to some `s₀` of norm `1`. For each `k`,
`s₀ / Q k - 1 = (s₀ - Q n) / Q k + (Q n / Q k - 1)` with `n ≥ k` large. The unit
`Q n / Q k` is the product of the `b i` with `k ≤ i < n`, so it belongs to the subgroup
`V_{c+1+k}`. Hence the additive second summand `Q n / Q k - 1` lies in `ϖ^{c+1+k} M`: its
coordinates have norm at most `r ^ (c+1+k)`. The first summand has small norm, so
`norm_coord_le_pow` controls its coordinates. Together these give
`isCompleteFiltration : IsCompleteFiltration (L ≃ₐ[K] L) D.unitFiltration` in the sense of
`Langlands.Cohomology.CompleteFiltration`.

## Approximation on graded pieces

`lin m u σ ∈ K` is the `σ`-coordinate of `ϖ^{-m} (u - 1)`. Then `IsNear m u` holds iff all
`lin m u σ` have norm (in `L`) at most `1` (`isNear_iff_lin`). Also `IsNear (m + 1) u`
holds iff they have norm at most `r` (`isNear_succ_iff_lin`). The subgroups
`normBall K L s hs = {k ∈ K | ‖algebraMap K L k‖ ≤ s}` of `K` express these congruences.
For `m > c` and `u, u'` near `1` at level `m`, the following hold modulo
`normBall K L r _`:

- `lin m (u * u') ≡ lin m u + lin m u'` (`lin_mul_mem`);
- `lin m (u / u') ≡ lin m u - lin m u'` (`lin_div_mem`).

Also `lin m (τ u) σ = lin m u (τ⁻¹ * σ)` (`lin_map`). The element
`1 + ϖ^m ∑ ρ, k ρ • basis ρ` has `lin` equal to `k` (`lin_sum`), and it is near `1` at
level `m` when the `k ρ` are integral (`isNear_sum`). Write
`O_K = normBall K L 1 _ = {k ∈ K | ‖algebraMap K L k‖ ≤ 1}`; then
`ϖ O_K = normBall K L r _` is a subgroup of it. Hence `V_m / V_{m+1}` behaves as the
coinduced module `Gal(L/K) → O_K / ϖ O_K`. `approx₁` and `approx₂` apply
`coinduced_approx₁` and `coinduced_approx₂` with `Y'' = normBall K L 1 _` (the
coordinates `lin m` of a cocycle with values in `V_m` lie in it) and
`Y' = normBall K L r _` (the congruences above hold modulo it). The result is a `0`- or
`1`-cochain with values in `V_m` whose coboundary agrees with the cocycle up to `V_{m+1}`.

`exists_coboundary1_eq_of_mem` and `exists_coboundary2_eq_of_mem` (under `[CompleteSpace L]`)
combine this with `exists_coboundary1_eq` and `exists_coboundary2_eq`. Every multiplicative
`1`-cocycle `f : Gal(L/K) → Lˣ` with values in `unitFiltration 0` is `g ↦ g • s / s` for
some `s ∈ unitFiltration 0`. Every multiplicative `2`-cocycle with values in
`unitFiltration 0` is `(g, h) ↦ g • s h / s (g * h) * s g` for a cochain `s` with values in
`unitFiltration 0`.

## Existence of the data

`exists_latticeData` assumes `[IsUltrametricDist L] [FiniteDimensional K L]
[IsGalois K L]`, a norm-preserving Galois action and `ϖ : K` with
`0 < ‖algebraMap K L ϖ‖ < 1`. It produces `D : LatticeData K L` with `D.ϖ = ϖ`. The basis
is Mathlib's normal basis `IsGalois.normalBasis K L`, scaled by the unit `ϖ^t` of `K`
(`Module.Basis.unitsSMul`) so that its vectors have norm at most `1`. The exponent `c`
comes from Cramer's rule. Let `A = (τ (basis σ))_{τ,σ}`. Then `det A ≠ 0`
(`det_ne_zero`): a vector `v ≠ 0` with `v ᵥ* A = 0` would give the relation
`∑_τ v τ • τ = 0` between the automorphisms, contradicting Dedekind's independence of
characters (`linearIndependent_monoidHom`). Also
`‖det A‖ · ‖coord x σ‖ ≤ ‖x‖` (`norm_det_mul_norm_coord_le`), from
`det A · coord x = adjugate A *ᵥ (τ x)_τ`. Here every entry of the adjugate has norm at
most `1` (`norm_det_le_one`, `norm_adjugate_le_one`, by the ultrametric expansion of
determinants). Then `c` is any exponent with `r ^ c < ‖det A‖`.

## Provenance

The module is derived from J. S. Milne, *Class Field Theory* v4.03 (2020), source
`milne-2020-class-field-theory` (PDF page = printed page + 9), Chapter III, printed p.104
(PDF p.113):

- Lemma 2.3: a normal basis with common denominators cleared spans a `G`-stable open
  lattice `V = ∑ O_K σ α` with `π^m O_L ⊆ V`, isomorphic to the induced module.
- Lemma 2.4: `U_L` contains a `G`-stable open subgroup with trivial cohomology.

Milne proves Lemma 2.4 in characteristic zero with the exponential map and refers to
Serre for a filtration proof. This module takes the filtration route in the
complete-ultrametric setting. The congruence subgroups `1 + ϖ^m M` have coinduced graded
pieces, and completeness lets the successive approximation converge. The norm-based
`LatticeData` interface, the Cramer bound and the coordinates `lin` are internal to this
formalization. The module asserts nothing about finiteness of `Lˣ / V` or about Herbrand
quotients; those are in `Langlands.ClassField.Global.LocalUnitHerbrandProof`.
