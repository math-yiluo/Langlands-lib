# Slab estimates in chamber coordinates of the minimal-parabolic height

Module `Langlands.Global.AdelicLocalFinitenessChamberSlabs` (namespace
`Langlands.Global.StandardConstantTerm`). Fix a connected reductive group `G` over a number
field `F`, a maximal split torus `i`, a generic cocharacter `ν`, the represented standard
minimal parabolic `p₀ = Standard.parabolicHom i ν ∅` and an Iwasawa compact `K` for `p₀`, with
height `H₀ = hK.height`. `Δ` is the set of simple relative roots.

## Invariance of the height

- `height_minimalParabolicImage_mul`: `H₀(l g) = H₀(g)` for `l` in the image `Λ₀` of `P₀(F)`
  (`height_rational_mul` after writing `l` as the image of a rational point of `P₀`).
- `height_standardUnipotent_mul`: `H₀(w g) = H₀(g)` for `w ∈ U_J(𝔸)`, `J ⊆ Δ`. The point `w`
  lies in `U_∅(𝔸)` (`standardParabolicOrder`), hence is the image of a point of the unipotent
  group `Standard.unipotentScheme i ν ∅` through `P₀`, and `height_unipotent_mul` applies.
- `height_cosetSubgroup_mul`: hence `H₀` is left invariant under `Λ₀ ⊔ U_J(𝔸)` (closure
  induction).

## Orthant weights, heights and shifts

For a type `X` with a coordinate map `c : X → (D → ℝ) × (Fin r → ℝ)` (root and central
coordinates), rates `ra`, `rb`, thresholds `τ`, a predicate `J` on `D` and an orthant
`ε : Fin r → Bool`:

- `orthantCoord ε j y` is `y` if `ε j` and `-y` otherwise;
- `orthantLogWeight ra rb ε x = ∑_β ra_β x_β + ∑_j rb_j orthantCoord ε j y_j` (a linear form);
- `leviRegion τ J = {x | x_β > τ_β for all β with J β}`;
- `orthantWeight c ra rb τ J ε g = exp(-2 orthantLogWeight(c g))` on `c⁻¹(leviRegion τ J)` and
  `0` elsewhere;
- for points `a_β`, `z_j` of a group `X`, `orthantShift a z J ε` sends a root direction
  `β ∉ J` to `a_β` and a central direction `j` to `z_j` if `ε j`, to `z_j⁻¹` otherwise;
- `orthantHeight c τ J ε` sends `β ∉ J` to `g ↦ (c g)_β - τ_β` and `j` to
  `g ↦ orthantCoord ε j ((c g)_j) + 1`;
- `orthantRate ra rb J` is `ra_β` on `β` and `rb_j` on `j`.

If `c(a_β g) = c(g) + e_β` and `c(z_j g) = c(g) + e_j` (unit vectors in the root, resp.
central, coordinates), then:

- `orthantHeight_shift`: the shift in direction `k` raises the height in direction `k` by one
  and leaves the other heights unchanged (`coords_inv_mul` treats `z_j⁻¹`);
- `orthantWeight_shift`: `W(g) = exp(2 orthantRate_k) W(shift_k g)`; the region
  `leviRegion τ J` is preserved because the root shifts are outside `J`.

Auxiliary results: `continuous_orthantLogWeight`, `measurableSet_leviRegion`,
`lowerMass_lt_pow` (if `f ≥ 1` and `∑_q ‖p_q‖ < f` then `∑_q ‖p_q‖ f^q < f^m`) and
`exists_rate_factor_gt` (for `c > 0` and any `M`, `√(exp(2R) c) ≥ 1` and `> M` for all large
`R`).

## The estimate `exists_orthantSlabEstimate`

`chamberCoords hK e g = e(H₀(g))` for a continuous linear equivalence `e` from the real
character dual of `P₀` to root and central coordinates; it is continuous
(`continuous_chamberCoords`) and invariant under `Λ₀ ⊔ U_J(𝔸)`
(`chamberCoords_cosetSubgroup_mul`). Assume `chamberCoords(a_β g) = chamberCoords(g) + e_β`,
`chamberCoords(z_j g) = chamberCoords(g) + e_j`, and that the `a_β` with `β ∉ J` and all `z_j`
commute with `L_J(𝔸)` and normalize `U_J(𝔸)` in both directions. Then for every orthant `ε`,
thresholds `τ` and bound `M` there is `R₀` such that for all rates `ra_β ≥ R₀`, `rb_j ≥ R₀`, all
degrees `m_k` and all coefficient families with `∑_q ‖p_{kq}‖ ≤ M`, there is `C ≥ 1` for which
the conclusion of `exists_slabEstimate` (module `AdelicStandardSlabEstimate`) holds for the
weight `orthantWeight`, the heights `orthantHeight` and the shifts `orthantShift` (with `J` the
predicate `β ∈ J`).

Proof: the hypotheses of `exists_slabEstimate` are checked one by one (measurability from
continuity of `chamberCoords`; invariance from `chamberCoords_cosetSubgroup_mul`; the weight
scaling with `κ_k = exp(2 orthantRate_k)` and the height shifts from the lemmas above; the
conditions on `z_j⁻¹` from those on `z_j`). For each direction `k` the Haar factor `c_k` of
conjugation on `U_J(𝔸)` is positive, `exists_rate_factor_gt` gives a rate `R_k` beyond which
the factor `√(κ_k c_k)` is at least `1` and exceeds `M`, and `R₀ = ∑_k |R_k|`; then
`lowerMass_lt_pow` gives the coefficient condition.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234 (literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`),
§7.5, Proposition, p. 219 (the corollary applied with `h = H₀ - T₀`, `σ_α` the translation by
`a_α` and `λ` sufficiently positive), and §7.7, pp. 220–221 (orthants of `𝔞_G`, weights
`w_{λ_ε}` on each orthant, translations by `z_j^{ε_j}` and the upended polynomials). The rates
`ra`, `rb` play the role of the coordinates of `λ`, and the requirement that `λ` be
sufficiently positive with respect to the coefficients of the polynomials is the threshold
`R₀`; the module uses the sufficient coefficient condition of `L2IndependentSlabs` instead of
BL's condition on the roots. The polynomials themselves are not constructed here.
