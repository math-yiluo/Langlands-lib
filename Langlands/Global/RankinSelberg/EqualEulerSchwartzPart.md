# The Schwartz–Bruhat factor under a one-place torus translation

Module `Langlands.Global.RankinSelberg.EqualEulerSchwartzPart`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualEulerSchwartz`.

## Purpose and provenance

These are internal auxiliary lemmas for the proof of
`Langlands.Global.RankinSelbergGlobal.EqualEulerFactorizationStatement` (Cogdell 2004, §2.3,
printed p.210, with Theorem 3.3, printed p.215). The module introduces no definitions and
assumes no unproved statement. From the module `WhittakerCellDecompositionStatement` it uses
only the definition `localPoint`, not the statement `WhittakerCellDecompositionStatement`.

Cogdell's Fields lectures (2003, Lecture 7 §3, printed pp.57–58) compute the unramified local
integral for `m < n` by writing `h = n ϖ^J k` (Iwasawa decomposition) and summing over
`J ∈ ℤ^m`. They then state that the same result holds for `GL_n × GL_n`, with the Schwartz
function taken to be the characteristic function `Φ°` of `𝒪^n`. In that equal-rank case one
needs `Φ°(e_n ϖ^J k) = 1[j_n ≥ 0]` for `k ∈ GL_n(𝒪)`, which the lectures leave implicit.
Cogdell 2004 (§4.1, p.220) uses this unramified computation at the places outside `S`. The
lemmas below prove the global form of that fact needed with the Library's one-place cell
decomposition (`WhittakerCellDecompositionStatement`): translating a class with
`g_v ∈ N_n(F_v) GL_n(𝒪_v)` on the left by `ι_v(ϖ^λ)` multiplies `Φ(e_n g)` by
`1[λ_n ≥ 0]`.

Notation: `n = r + 1`; `e_n g` is `lastRow F r g` (module `EqualIntegrals`), the last row of
`g ∈ GL_n(𝔸)` as an adelic row vector; `g_w = finiteComponent F n w g` is the component of
`g` at the finite place `w` (module `PartialWhittakerIntegrals`); `x_w = localCoordinates F n
w x` are the `F_w`-coordinates of a row vector `x` (module `SchwartzBruhat`).
`IsStandardOutside F n S Φ` (module `SchwartzBruhat`) means: `Φ` vanishes off
`integralOutside F n S` (the row vectors with `x_w ∈ 𝒪_w^n` for every finite `w ∉ S`), and on
that set `Φ(x)` depends only on the archimedean coordinates of `x` and on `x_w` for `w ∈ S`.
`IsUnipotentIntegral F n v x` means `x ∈ N_n(F_v) GL_n(𝒪_v)`, stated as: `x k` is upper
unitriangular for some `k ∈ GL_n(𝒪_v)`. `torus ϖ λ = diag(ϖ^(λ_1), …, ϖ^(λ_n))`.

## Results

- `lastRow_fst g j`: the archimedean part of the `j`-th coordinate of `e_n g` is the `(n, j)`
  entry of the infinite component of `g`. Holds by definition (`rfl`).

- `localCoordinates_lastRow w g j`: `(e_n g)_w` has `j`-th coordinate `(g_w)_(n, j)`, that is,
  `(e_n g)_w` is the last row of `g_w`. Holds by definition (`rfl`).

- `RankinSelbergGlobal.finiteComponent_mul F n w g g'`: `(g g')_w = g_w g'_w`. Both maps in the definition of
  `finiteComponent` are monoid homomorphisms.

- `lastRow_mul_fst (hinf) g j`: if the infinite component of `h` is `1`, then `e_n (h g)` and
  `e_n g` have the same archimedean coordinates.

- `localCoordinates_lastRow_mul_of_eq_one (hw : h_w = 1) g`: `(e_n (h g))_w = (e_n g)_w`.

- `localCoordinates_lastRow_mul_torus (hv : h_v = torus ϖ λ) g j`:
  `(e_n (h g))_v` has `j`-th coordinate `ϖ^(λ_n) · ((e_n g)_v)_j`. Proof: the last row of
  `diag(ϖ^λ) g_v` is `ϖ^(λ_n)` times the last row of `g_v` (`Matrix.diagonal_mul`).

- `lastRow_integral_primitive (hx : IsUnipotentIntegral F n v x)`: every entry of the last row
  of `x` lies in `𝒪_v`, and some entry has valuation `1` (a primitive vector of `𝒪_v^n`).
  Proof: with `u = x k` upper unitriangular, the last row of `u` is `e_n`, so the last row of
  `x = u k⁻¹` is the last row of `k⁻¹ ∈ GL_n(𝒪_v)`, which is integral. If all its entries had
  valuation `< 1`, the `(n, n)` entry `∑_j (k⁻¹)_(n, j) k_(j, n) = 1` of `k⁻¹ k` would have
  valuation `< 1` by the ultrametric inequality (`Valuation.map_sum_lt`), a contradiction.

- `apply_lastRow_mul_torus (hΦ : IsStandardOutside F n S Φ) (hvS : v ∉ S) (hϖ : |ϖ|_v < 1) λ
  (hinf) (hfin) (hv) (hg)`: let `h ∈ GL_n(𝔸)` have infinite component `1`, component `1` at
  every finite place `w ≠ v` and component `torus ϖ λ` at `v`, and let
  `g_v ∈ N_n(F_v) GL_n(𝒪_v)`. Then

  `Φ(e_n (h g)) = if 0 ≤ λ_n then Φ(e_n g) else 0`.

  Proof. By `lastRow_integral_primitive`, `(e_n g)_v` is integral and has a coordinate of
  valuation `1`, and `(e_n (h g))_v = ϖ^(λ_n) (e_n g)_v`. If `λ_n < 0`, that coordinate of
  `(e_n (h g))_v` has valuation `|ϖ|_v^(λ_n) > 1`, so `e_n (h g)` is not in
  `integralOutside F n S` (because `v ∉ S`) and `Φ` vanishes there. If `λ_n ≥ 0`, both
  `(e_n (h g))_v` and `(e_n g)_v` are integral and the coordinates at every other finite place
  and at infinity agree. So `e_n (h g)` and `e_n g` are together in or out of
  `integralOutside F n S`. In the first case the second clause of `hΦ` gives equality (the
  archimedean coordinates and the coordinates at the places of `S` agree), in the second
  case both values are `0`.

- `apply_lastRow_localPoint_torus (hΦ) (hv : v ∉ S) ϖ (hϖ) λ g (hg)`: the same identity for
  `h = ι_v(ϖ^λ) = localPoint F n v (torus ϖ λ)` (module
  `WhittakerCellDecompositionStatement`) and for `ϖ` a uniformizing element of `F_v` for
  `Valued.v` (`GeneralLinear.Iwasawa.IsUniformizingElement`, whose first clause is
  `|ϖ|_v < 1`):

  `Φ(e_n ι_v(ϖ^λ) g) = if 0 ≤ λ_n then Φ(e_n g) else 0` whenever `g_v ∈ N_n(F_v) GL_n(𝒪_v)`.

  Proof: `localPoint` is `adelicEquiv.symm (ofFinite (localInclusion v (torus ϖ λ)))`, so its
  infinite component is `1`, its finite component is `localInclusion v (torus ϖ λ)`, and the
  component of that at `w` is `torus ϖ λ` for `w = v` and `1` for `w ≠ v`
  (`FiniteAdelicGL.localProjection_localInclusion` and `…_of_ne`). Then apply
  `apply_lastRow_mul_torus`.

## Scope

Only the uniformizer's first clause, `|ϖ|_v < 1`, is used. The result says nothing about the
Whittaker factors or the determinant factor of the integrand; those are separate pieces of the
proof of the Euler factorization.

The finite-component multiplication identity is imported from
`PartialIntegralExhaustion`.
