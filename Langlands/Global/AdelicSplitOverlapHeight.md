# A height comparison for two Siegel factorizations in Bruhat position

Author: Worker 2.

This internal helper module formalizes the height half of the proof of
Springer's overlap estimate (Springer, *Reduction theory over global fields*,
1994, Proposition 2.6, printed p. 213). Two Siegel factorizations
`x i(s) p = x' i(s') p' γ` are compared through a coordinate line preserved by
the minimal parabolic, where `γ` is a rational point in Bruhat position
`b₁ n b₂`. The comparison bounds the Weyl translate `n · ψ` of the line character
at `s'` by a constant times `ψ` at `s`. The provenance is derived. Springer's
argument applies heights to the line `e` and to its rational image `γ e`. Here
that argument is carried out with the Library's published orbit heights,
compact height bounds, a positive lower bound for the heights of nonzero rational
vectors, and the compact rational cover of the minimal parabolic. Unlike
Springer, the module asserts nothing about the shape of the line character; see
the errata note `notes/errata/springer-1994-reduction-global-fields.md`.

All declarations are in namespace `Langlands.Global.AdelicSiegelFactors`, over a
number field `F`.

## Auxiliary declarations

* `rational_basePointEquiv_comp`: if `c` is a base point of a subgroup `H → G`,
  the principal adelic point of its image in `G` is the image of the rational
  norm-one point `rationalNormOne F H (basePointEquiv c)`.
* `lineCharacterNorm_eq_normCharacter`: the published `lineCharacterNorm` of a
  torus-preserved line is, by definition, `PositiveRealTorus.normCharacter` of the
  torus line character in the character lattice.
* `torusEmptyParabolicFactor` and `torusEmptyParabolicFactor_comp`: the torus map
  factors through the minimal standard parabolic `P_∅`. The factor comes from the
  published containments torus ⊆ Levi ⊆ parabolic.
  `map_torusEmptyParabolicFactor` states the corresponding identity on adelic
  points.

## Main theorem

`exists_bruhat_height_bound` assumes the following:

* `G` is affine and connected reductive;
* `i` is a monomorphic maximal split torus that is also a maximal torus;
* `ν` is generic;
* `ρ` is a matrix representation whose coordinate line `j` is preserved by `P_∅`
  and by the torus, with torus line character `ψ`;
* `C ⊆ G(A)` is compact.

It gives `D > 0` with the following property. Let `x, x' ∈ C`, let `s, s'` be
adelic torus points, and let `p, p'` lie in the norm-one subgroup of `P_∅`. Let
`n` be a normalizer point and `b₁, b₂` base points of `P_∅`. If

`x · i(s) · p = x' · i(s') · p' · rational(b₁ n b₂)`,

then `|(n · ψ)(s')| ≤ D · |ψ(s)|`. Here `|·|` is
`PositiveRealTorus.normCharacter` and `n · ψ` is the published `weylAction`.

No norm-one condition is imposed on `s` or `s'` in this theorem. The norm-one
conditions on `p` and `p'` are used.

### Proof

Let `e` be the coordinate vector of `j`, and let `H(v, g)` denote the published
`orbitHeight F G ρ v g`.

1. *Rewriting the right side.* Write `b₁ = c₁` and `b₂ = c₂` as base points of
   `P_∅`. Move `i(s')` past `n` by
   `AdelicGroupPoints.exists_map_mul_rational_normalizer`, which gives `t'` with
   `i(s') n = n i(t')` and `|χ(t')| = |(n · χ)(s')|`. Write `sP` for the image of
   `s'` in `P_∅(A)`. The conjugate `y = sP · (p' c₁) · sP⁻¹` lies in the normal
   norm-one subgroup of `P_∅`. The published compact cover
   `hasCompactNormOneRationalCover_emptyParabolic_of_maximalTorus` gives a
   rational `r ∈ P_∅(F)` with `ω = r · y⁻¹ ∈ Ω` for a fixed compact `Ω`. Thus
   the right side equals `k · rational(g) · i(t') · c₂`, where `g = r n` is
   rational and `k = x' ω⁻¹` lies in the compact set `K = C · Ω⁻¹`.
2. *Heights of both sides.* Right translation by norm-one points of `P_∅`
   preserves `H(e, ·)` (`orbitHeight_mul_map_normOne`). Right translation by
   `i(t)` multiplies it by the line-character norm
   (`orbitHeight_mul_map_eq_lineCharacterNorm`). Right translation by a rational
   point moves the vector (`orbitHeight_mul_rational`). Hence
   `H(e, left side) = |ψ(s)| · H(e, x)` and
   `H(e, right side) = |(n · ψ)(s')| · H(v, k)`, where `v = ρ(g) e ≠ 0` is a
   rational vector.
3. *Bounds.* The published `exists_pos_orbitHeight_bounds_of_isCompact` gives
   `H(e, x) ≤ B₁ · H(e, 1)` for `x ∈ C`, and `H(v, 1) ≤ B₂ · H(v, k)` for
   `k ∈ K` and all nonzero `v`. The published
   `PrimitiveAdelicHeight.exists_pos_le_rationalHeight` gives `h₀ > 0` with
   `h₀ ≤ H(v, 1)` for every nonzero rational `v`. Combining these with step 2
   gives
   `|(n · ψ)(s')| · h₀ ≤ B₂ · |ψ(s)| · H(e, x) ≤ B₁ B₂ H(e, 1) · |ψ(s)|`.
   So `D = B₁ B₂ H(e, 1) / h₀` works.

The main theorem is elaborated with `maxHeartbeats 1600000`, set only for that
declaration.
