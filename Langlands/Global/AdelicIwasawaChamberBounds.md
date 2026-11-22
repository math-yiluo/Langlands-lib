# Compact translation bounds and weights in Iwasawa height coordinates

`IwasawaHeightCoordinateRightShiftStatement` bounds the change of any finite family of continuous real-linear coordinates of the Iwasawa height under right multiplication by a compact set `C`. The bound holds at every adelic point. If a coordinate is bounded below by `t` before multiplication, it is bounded below by `t − b` afterwards, where `b` is the common bound. Upper cutoffs shift by `+b`.

The height addition law writes the increment at `x` under multiplication by `a ∈ C` as the height of `ka` for some `k` in the Iwasawa compact subgroup `K`. The proof bounds the sum of the absolute values of the coordinates on the compact set `KC`.

`IwasawaFiniteMaximumWeightStatement` concerns the log weight `ell(H) = max_j ⟨λ_j,H⟩` for a nonempty finite family of real character parameters. The log weight is continuous. For a positive-rank closed matrix representation, `exp(ell(H_P(g)))` is bounded above by `A H(g)^r` for `A > 0` and `r ≥ 0`, where `H` is the adelic representation height. There is also a uniform bound on the absolute difference of the log weight under right multiplication by any fixed compact set.

The proof complexifies each real parameter and applies the existing polynomial estimate for a single height power. Taking maxima of its coefficients and exponents gives the same upper bound for each family member, since the representation height is at least one. The coordinate displacement lemma bounds the change in each member of the maximum, and bounding the change in both directions gives the absolute difference estimate. The sign lemma writes one linear pairing plus a sum of absolute values of linear pairings as a finite maximum, by taking the sign of each coordinate.

These are derived estimates for the weight and chamber steps of Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024). The height increments implement the compact right translation bound of (7.1), used in the proof of §7.4, Lemma (2), pp. 215–216. The finite maximum includes the symmetric choice of linear weights on the central orthants of §7.7, pp. 220–221.
