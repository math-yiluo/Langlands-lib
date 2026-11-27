# Bounds for the terms of the alternate splitting formula

Module `Langlands.LinearAlgebra.GMFamilyOrthogonalSetBounds` bounds the two
kinds of terms in the proof of Lapid's Lemma 8, for a positive
`(G, M)`-orthogonal set `Y` with `⟪v, Y_P⟫ ≥ t ≥ 0` for all chambers `P` and
simple roots `v`, a point `ξ ∈ V = 𝔞_M^G` off the walls, and a Schwartz test
`u` on `V` with `(1 + ‖H‖)^{n + dim V + 1} |phaseFourier u H| ≤ A`.

## Results

- `isFamily_exp_of_orthogonal`: `P ↦ e^{λ(Y_P)}` is a `(G, M)`-family. For
  adjacent chambers `Y_P − Y_{P'} = r v`, and `Λ(v) = 0` on the common wall.
- `orthant_point_eq`, `inner_simpleRoot_projection`, `orthantSign_abs`:
  the points of the orthant formula in `chamberBasis` coordinates; the
  projection to `V` does not change inner products with simple roots;
  `|orthantSign d| = 1`.
- `exists_face_term_bound` (proper faces): for a face `Q = posSet R w ≠ ∅`
  there is `C` with
  `|∫_V c_M^Q(Λ_x) u(x) dx| ≤ C A (1 + t)^{−n}`,
  `c_M^Q = cQM R a c Q` for the exponential family `c`. By
  `integral_cM_exp_eq_orthants` for the Levi roots of `Q` and the family
  `S ↦ Y(Q ∪ S)`, the integral is a sum over chambers `S` of `M_Q` of orthant
  integrals in the coordinates of `Δ_S ⊆ Δ_{Q ∪ S}`. Since `Q ≠ ∅`, some
  simple root `β` of `Q ∪ S` is not in `Δ_S` (`exists_simpleRoot_not_mem_face`),
  so the `β`-coordinate is not moved and `exists_orthant_term_bound` applies to
  each orthant.
- `exists_main_term_bound` (the full family): there is `C` with
  `|(2π)^{−dim V} ∫_V c_M(Λ_x) u(x) dx − u(0)| ≤ C A (1 + t)^{−n}`.
  Let `P₀ = posSet R (−ξ)`, a chamber because `−ξ` is regular. By
  `integral_cM_exp_eq_orthants` with `R' = R`, the integral is
  `∑_P gram(P) · orthantSign · ∫_{orthant_P} F_P`, the orthant of `P` being
  `{⟪v, −ξ⟫ X_v > 0}`. For `P = P₀` this is the positive orthant, with sign
  `1`; writing it as the integral over all of `ℝ^{Δ_{P₀}}` minus that over the
  complement, the full integral is
  `gram(P₀)⁻¹ ∫_V phaseFourier u = gram(P₀)⁻¹ (2π)^{dim V} u(0)`
  (`integral_eq_gramVolume_mul`, `integral_phaseFourier`), and on the
  complement some coordinate is `≤ 0`. For `P ≠ P₀` some simple root of `P` is
  negative at `−ξ` (otherwise `P₀ ⊆ P` and `P = P₀` by
  `parabolic_eq_of_subset`), so on its orthant that coordinate is negative.
  In both cases `exists_orthant_term_bound` gives the decay.

## Provenance

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), §7, proof of Lemma 8,
pp. 326–327, estimates (16) and (17)
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`).
`exists_face_term_bound` corresponds to (16) for `Q₁ ≠ G`, and
`exists_main_term_bound` to the treatment of the term `Q₁ = G`, where Lapid
splits `∫ χ_M(T, H) φ_P(H) dH` into `∫ φ_P = d_P(0)` (17) and a remainder;
here the convex hull `χ_M` is replaced by the signed orthants. Arthur's
positive orthogonal sets and the family `e^{λ(Y_P)}` are from J. Arthur,
*An introduction to the trace formula*, §17, p. 94
(`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`).
