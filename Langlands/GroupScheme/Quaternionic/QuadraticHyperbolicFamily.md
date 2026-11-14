# Hyperbolic families of a nondegenerate quaternionic quadratic form

Author: Worker 350.

Module `Langlands.GroupScheme.Quaternionic.QuadraticHyperbolicFamily`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution`.

## Setting

`K` is a field (of any characteristic, finite or infinite), `D` a division `K`-algebra,
`σ : FirstKindInvolution K D`, `n` a finite index type and `q` a `σ`-quadratic form on row
vectors `D^n`, i.e. a class in `M_n(D) / {X - ᵗX^σ}` (published in `Quaternionic.Forms`).
`h = σ.sesqForm (σ.polar q)` is its polar sesquilinear form, `q(x) = σ.quadraticValue x q`
takes values in `D / {d - σ d}`, and `σ.quadraticWittIndex q` is the largest `D`-dimension of a
totally singular subspace. For row vectors `x, y`, the published
`σ.hyperbolicLineMatrix q x y` is the matrix of the row map `z ↦ h(z, y) x`
(`vecMul_hyperbolicLineMatrix`).

## Definition

`IsHyperbolicFamily q x y` (for families `x y : ι → D^n`) is the conjunction of
`q(xₖ) = 0`, `q(yₖ) = 0`, `h(xₖ, yₗ) = δₖₗ`, `h(xₖ, xₗ) = 0` and `h(yₖ, yₗ) = 0` for all
indices `k, l`. So each `(xₖ, yₖ)` is a hyperbolic pair (`isHyperbolicPair`, in the sense of the
published `IsHyperbolicPair`), and distinct pairs are polar-orthogonal. This is the standard
notion of a hyperbolic (Witt) basis of a hyperbolic subspace: an internal auxiliary definition
used to build split tori; it is not cited from a specific source.

## Results

- `sesqForm_sum_smul_left`, `sesqForm_sum_smul_right`: `h` is additive over finite sums, with
  `h(∑ cₖ uₖ, w) = ∑ cₖ h(uₖ, w)` and `h(w, ∑ cₖ uₖ) = ∑ h(w, uₖ) σ(cₖ)`.
- `IsTotallySingular.sesqForm_polar_eq_zero`: the polar form vanishes on a totally singular
  subspace. Proof: `q(u + σ(a) v) = q(u) + q(v) + [h(u, v) a]`, so `[h(u, v) a] = 0` for every
  `a`, and `eq_zero_of_forall_mul_mem_alternatingSubspace` gives `h(u, v) = 0`.
- `exists_polar_dual_family`: for nondegenerate `q` and a linearly independent finite family
  `x`, there is `z` with `h(xₖ, zₗ) = δₖₗ`. Proof: the map `Ψ : z ↦ (h(z, xₖ))ₖ` to `D^ι` is
  surjective. Otherwise `Submodule.exists_le_ker_of_lt_top` gives a nonzero functional `f`
  vanishing on its range; writing `f(v) = ∑ vₖ cₖ`, the vector `v = ∑ σ(cₖ) xₖ` is
  polar-orthogonal to everything, so `v = 0` by nondegeneracy (`exists_polar_partner`), and
  linear independence forces all `cₖ = 0`, contradicting `f ≠ 0`. Preimages of the standard
  basis vectors give `z`, and `sesqForm_polar_swap` converts `h(zₗ, xₖ)` to `h(xₖ, zₗ)`.
- `exists_isHyperbolicFamily`: a nondegenerate `q` has a hyperbolic family indexed by
  `Fin (σ.quadraticWittIndex q)`. Proof: take a maximal totally singular `W`
  (`exists_maximal_totallySingular`), a basis `x` of `W`, and a polar-dual family `z`. Set
  `yₗ = zₗ + ∑ₖ cₗₖ xₖ`, where `cₗₖ = -h(zₗ, zₖ)` for `l < k`, `cₗₗ = -σ(sₗ)` for a
  representative `sₗ` of `q(zₗ)`, and `cₗₖ = 0` for `l > k`. Since `W` is totally singular
  and the `xₖ` are polar-dual to the `zₗ`, one gets `h(xₖ, yₗ) = δₖₗ`,
  `h(yₖ, yₗ) = h(zₖ, zₗ) + σ(cₗₖ) + cₖₗ` and `q(yₗ) = [sₗ] + [σ(cₗₗ)] = 0`; the choice of `c`
  makes `h(yₖ, yₗ)` vanish for `k < l` and `k > l` (using `h(z, w) = σ h(w, z)`). For `k = l`,
  `sesqForm_polar_self_eq_zero` applies.
- `IsHyperbolicFamily.comp`: reindexing along an injective map preserves the property.
  `IsHyperbolicFamily.polar_right_left`: `h(yₖ, xₗ) = δₖₗ`.
- `hyperbolicLineMatrix_mul_of_eq_zero`, `hyperbolicLineMatrix_mul_of_eq_one`: writing
  `L(a, b)` for `hyperbolicLineMatrix q a b`, `L(a, b) L(c, d) = 0` if `h(a, d) = 0`, and
  `L(a, b) L(c, d) = L(c, b)` if `h(a, d) = 1` (checked on row vectors with
  `Matrix.ext_of_single_vecMul`).
- `IsHyperbolicFamily.lineMatrix_mul_left_left`, `lineMatrix_mul_left_right`,
  `lineMatrix_mul_right_left`, `lineMatrix_mul_right_right`: for `Pₖ = L(xₖ, yₖ)` and
  `P'ₖ = L(yₖ, xₖ)`, `Pₖ Pₗ = δₖₗ Pₖ`, `P'ₖ P'ₗ = δₖₗ P'ₖ` and `Pₖ P'ₗ = P'ₖ Pₗ = 0`.
  `lineMatrix_ne_zero`: `Pₖ ≠ 0`, because `xₖ Pₖ = xₖ ≠ 0`.
- `IsHyperbolicPair.lineMatrix_congr_mem`: for a hyperbolic pair `(x, y)`, `P = L(x, y)` and
  any representative `Q` of `q`, `P Q ᵗP^σ ∈ {X - ᵗX^σ}`. The class of `P Q ᵗP^σ` is the
  pullback form `z ↦ q(z P) = q(h(z, y) x) = 0`, and `eq_zero_of_forall_quadraticValue_eq_zero`
  shows that a form with all values `0` is `0`.
- `IsHyperbolicPair.lineMatrix_polar_mem`: with also `P' = L(y, x)`,
  `P Q + Q ᵗP^σ - P Q ᵗP'^σ - P' Q ᵗP^σ ∈ {X - ᵗX^σ}`. Proof: by `noncomm_ring` this matrix is
  `(1 + P) Q ᵗ(1 + P)^σ - Q - (P + P') Q ᵗ(P + P')^σ + P' Q ᵗP'^σ`, whose class is the form
  `z ↦ q(z + h(z, y) x) - q(z) - q(h(z, y) x + h(z, x) y) + q(h(z, x) y)`.
  Using `q(x) = q(y) = 0`, `h(x, y) = 1` and `IsHyperbolicPair.quadraticValue_plane`, every
  value is a difference of the classes of `h(z, y) σ(h(z, x))` and `h(z, x) σ(h(z, y))`, which
  is `0` because `[d] = [σ d]` in `D / {d - σ d}`.

## Provenance and scope

Internal derived module. It uses the published Witt index, totally singular subspaces,
hyperbolic pairs and hyperbolic line matrices. The construction of a hyperbolic family from a
maximal totally singular subspace and a dual family follows the standard proof of Witt
decomposition. Only `D` being a division ring and `q` nondegenerate are used: no centrality,
type, characteristic or infinitude hypothesis.
