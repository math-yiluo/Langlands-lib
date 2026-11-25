# Entrywise congruence neighbourhoods in `GL_n` of an ultrametric normed field

`Langlands.Group.GL.NormCongruence`. Namespace `Langlands.GeneralLinear`.

The elementary estimates near `1` in `GL_n(𝕂)` for a normed field `𝕂` with an ultrametric norm
(`[NormedField 𝕂] [IsUltrametricDist 𝕂]`; `[ProperSpace 𝕂]` where compactness or limits are
needed). All bounds are entrywise: a matrix `M` is bounded by `c` when `‖M i j‖ ≤ c` for all `i, j`
(the private predicate `Bd`). In the base-change files `𝕂` is a nonarchimedean local field `F`
(normed by `LocalGalois.localNormedField`) or a finite extension `E` of it with the spectral norm
(`LocalGalois.finiteExtensionNormedField`).

## Statements

- `normCongruence 𝕂 n r : Set (GeneralLinear n 𝕂)`, the set of `g` with
  `‖(g : Matrix (Fin n) (Fin n) 𝕂) i j - (1 : Matrix (Fin n) (Fin n) 𝕂) i j‖ ≤ r` for all `i, j`;
  `mem_normCongruence`, `normCongruence_mono`, `one_mem_normCongruence` (`0 ≤ r`),
  `mul_mem_normCongruence` (`0 ≤ r ≤ 1`), `inv_mem_normCongruence` (`0 ≤ r < 1`).
- `normCongruenceSubgroup 𝕂 n (hr₀ : 0 ≤ r) (hr : r < 1) : Subgroup (GeneralLinear n 𝕂)` with
  carrier `normCongruence 𝕂 n r` (`coe_normCongruenceSubgroup`, `mem_normCongruenceSubgroup`).
- `isOpen_normCongruence (hr : 0 < r)`; `isCompact_normCongruence [ProperSpace 𝕂] (hr₀ : 0 ≤ r)
  (hr : r < 1)`.
- `map_mem_normCongruence_iff (τ : 𝕂 →+* 𝕃) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (g)`:
  `Matrix.GeneralLinearGroup.map τ g ∈ normCongruence 𝕃 n r ↔ g ∈ normCongruence 𝕂 n r`.
- `mul_eq_mul_of_pow_mul_eq_mul_pow (hr₀ : 0 ≤ r) (hq : r < ‖(q : 𝕂)‖)`: for matrices `A`, `B`
  with `‖(A - 1) i j‖ ≤ r`, `‖(B - 1) i j‖ ≤ r` and any matrix `g`, `A ^ q * g = g * B ^ q` implies
  `A * g = g * B`.
- `conj_eq_of_conj_pow_eq`: for `u, v ∈ normCongruence 𝕂 n r`, `r < ‖q‖`, and `g ∈ GL_n(𝕂)`,
  `g⁻¹ * u ^ q * g = v ^ q → g⁻¹ * u * g = v`; `eq_of_pow_eq`: `u ^ q = v ^ q → u = v`.
- `pow_mem_normCongruence`: `u ∈ normCongruence 𝕂 n r → u ^ q ∈ normCongruence 𝕂 n (r * ‖(q : 𝕂)‖)`
  (`0 ≤ r < ‖q‖`).
- `exists_pow_eq [ProperSpace 𝕂]`: every `g ∈ normCongruence 𝕂 n (r * ‖(q : 𝕂)‖)` is `u ^ q` for
  some `u ∈ normCongruence 𝕂 n r` (`0 ≤ r < ‖q‖`).
- `exists_mul_eq_twistedConj [ProperSpace 𝕂] (τ : 𝕂 →+* 𝕂) (hτ : ∀ x, ‖τ x‖ = ‖x‖)
  (hτq : ∀ x, τ^[q] x = x) (hρ₀ : 0 ≤ ρ) (hρr : ρ ≤ r) (hq : r < ‖(q : 𝕂)‖)`: for
  `u₀ ∈ normCongruence 𝕂 n r` and `g ∈ normCongruence 𝕂 n (ρ * ‖q‖)` there are
  `κ ∈ normCongruence 𝕂 n ρ` and `u ∈ normCongruence 𝕂 n ρ` with
  `Matrix.GeneralLinearGroup.map τ u = u` and `u₀ * g = κ⁻¹ * (u₀ * u) * map τ κ`.

## Proofs

- Subgroup: `(1 + A)(1 + B) - 1 = A + B + AB`; for the inverse `N = g⁻¹ - 1` one has
  `N = -A - AN`, and at an entry of largest norm `t ≤ max (r, r t)` forces `t ≤ r` since `r < 1`.
  Openness: closed balls of an ultrametric space are open. Compactness: the entrywise ball of radius
  `r` around `1` is a compact submonoid of matrices, and the units of a compact submonoid form a
  compact set (Mathlib's `Submonoid.units_isCompact`).
- Intertwining: with `D = A g - g B`, the telescoping identity bounds
  `A^m g - g B^m - m D` by `r · max‖D‖`; for `m = q` the left side is `-q D`, so
  `‖q‖ max‖D‖ ≤ r max‖D‖` and `D = 0`.
- Powers: `(1 + M)^m - 1 - m M` is bounded by `a²` when `M` is bounded by `a ≤ 1`.
- Roots: the iteration `X ↦ X - q⁻¹((X + 1)^q - g)` gives a decreasing sequence of nonempty closed
  sets inside a compact ball on which `(X + 1)^q - g` is bounded by `(r/‖q‖)^k r ‖q‖`; a point of the
  intersection is a root. Uniqueness is the intertwining lemma with `g = 1`.
- Twisted descent: `t x = q⁻¹ ∑_{j<q} τ^j x` is `τ`-fixed, `p x = q⁻¹ ∑_{j<q} j τ^j x`, and
  `x = t x + τ(p x) - p x`, with `‖t x‖, ‖p x‖ ≤ ‖x‖/‖q‖`. Writing `u₀ = 1 + A`, `g = 1 + X`, the map
  `Y ↦ X + AX + K(Y)(A + X + AX) - U(Y) S(Y) - A U(Y) - A S(Y) - A U(Y) S(Y)` (with `U`, `K`, `S` the
  entrywise `t`, `p`, `τ ∘ p`) is a contraction with constant `r/‖q‖` of the entrywise ball of radius
  `ρ‖q‖`; at its fixed point `Y`, `κ = 1 + K(Y)`, `u = 1 + U(Y)` satisfy
  `κ u₀ g = u₀ u τ(κ)`. The fixed point exists by nested compact balls (completeness would do as
  well). The centre `u₀` need not be `τ`-fixed.

## Declarations, in order

private: `Bd`, `Bd.mono`, `Bd.zero`, `Bd.add`, `Bd.neg`, `Bd.sub`, `Bd.mul`, `Bd.smul`, `Bd.nsmul`,
`Bd.one`, `Bd.of_sub_one`, `Bd.pow`, `Bd.pow_sub_one`, `Bd.tele`; public
`mul_eq_mul_of_pow_mul_eq_mul_pow`; private `Bd.pow_sub_pow`, `isClosed_bd`, `isCompact_bd`,
`le_zero_of_le_pow`, `exists_limit`, `exists_fixed`, `Bd.isUnit`, `Bd.inv`; public
`normCongruence`, `mem_normCongruence`, `normCongruence_mono`, `one_mem_normCongruence`,
`mul_mem_normCongruence`, `inv_mem_normCongruence`, `normCongruenceSubgroup`,
`coe_normCongruenceSubgroup`, `mem_normCongruenceSubgroup`, `isOpen_normCongruence`,
`isCompact_normCongruence`, `map_mem_normCongruence_iff`, `pow_mem_normCongruence`,
`conj_eq_of_conj_pow_eq`, `eq_of_pow_eq`, `exists_pow_eq`; section `Descent`: private
`exists_twisted_decomposition`, public `exists_mul_eq_twistedConj`.

## Literature

J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Annals of Mathematics Studies 120 (1989), Chapter 1, §3: before the proof of Lemma 3.2,
p. 21 ("the map `t ↦ t^l` is an isomorphism in a neighborhood of 1"), and in the proof of Lemma 3.4,
p. 24 ("the map `m ↦ m^l` is a conjugacy-preserving diffeomorphism from an invariant neighborhood
of 1 onto its image"). These are the facts that `pow_mem_normCongruence`, `exists_pow_eq` and
`conj_eq_of_conj_pow_eq` make explicit with a radius; the twisted descent is the near-identity form
of the surjectivity of `t ↦ t^{1-σ}` used on p. 21 (Hilbert's Theorem 90 for a torus). The proofs
here are the elementary estimates of the source, not the exponential map of Arthur–Clozel.

## Source and licence

Port of the following files of the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`, all under
`src/Development/AutomorphicArithmetic/Foundations/Convolution/TwistedLocalOrbits/`:
`RootConj.lean` lines 5–93 (`Bd`, `Bd.tele`, `intertwine`, `rootConj`), `RootEx.lean` lines 7–194
(`Bd.pow_sub_pow`, `exists_root`, `root_unique`, `rootEx`), `ValuationNatCastLeOne.lean` lines
9–153 (`Bd.pow`, `Bd.inv`, `ballSub`, `isOpen_ball`, `isCompact_ball`, `pow_mem_ball`,
`sg_mem_ball_iff`), `OpenNear.lean` lines 5–263 (`lim_ex`, `eq_zero_of_le_pow`, `fix_ex`, `lin_ex`,
`Bd.isUnit`, `openNear`). The repository has no licence file; its text is used with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

Changes against the source:

- Valuations `valuation E : E → ValueGroupWithZero E` of a nonarchimedean local field are replaced
  by the norm of any ultrametric normed field, with real bounds; nonnegativity of the bounds is
  carried explicitly (`Bd.mul`, `Bd.zero`), and `eq_zero_of_le_pow` (archimedean value group) by a
  limit in `ℝ`.
- The source's `ball n r` and `ballSub` become `normCongruence 𝕂 n r` and `normCongruenceSubgroup`;
  `isCompact_ball` is proved through `Submonoid.units_isCompact` instead of the source's topology
  facts on `GL_n`; `sg_mem_ball_iff` becomes `map_mem_normCongruence_iff` for any isometric ring
  homomorphism.
- `exists_fixed_root` (roots of σ-fixed elements via uniqueness) is not needed: roots are taken
  directly in `GL_n` of the base field; `exists_pow_eq` and the uniqueness `eq_of_pow_eq` replace
  `rootEx`.
- `openNear` takes an isometric ring endomorphism `τ` with `τ^[q] = id` instead of the structure
  `Cyc`, and drops its unused hypothesis that `u₀` is fixed.
- Names follow the Library; docstrings added.
