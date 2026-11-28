# The family comparison under rational conjugation of the target parabolic

Module `Langlands.Global.AdelicEisensteinFamilyConjugateTarget` proves
`FamilyRegularComparison.of_conjugateTarget`.

## Statement

Let `(w, c)` be a Weyl conjugation from `P` to `Q`, `s` a rational point of `G`, and
`q ≫ Int(s)` the conjugate parabolic `s Q s⁻¹` (`G.innerIso s`), presented by
`r'.compAmbientIso (G.innerIso s)`. Assume that `iU` and `iV` are geometric unipotent radicals,
`l'` is a rational Levi subgroup, and `K` has Iwasawa coverage for `P`, `Q` and `s Q s⁻¹`. Then
the family comparison (predicate of module
`Langlands.Global.AdelicEisensteinFamilyRegularComparison`) for `(P, s Q s⁻¹)` with the Weyl
representative `s w` implies the family comparison for `(P, Q)` with `w`. The Levi data `l'`,
`c` and `π'` are unchanged.

## Proof

Write `t` for the adelic point of `s` (`innerAdelicPoint`) and `W = weylParameter l c π'`.
Fix the data for `(P, Q)`.

- `intertwiningConjugateTarget` (module `Langlands.Global.AdelicIntertwiningConjugateTarget`)
  gives `M_{sQs⁻¹}(s w, λ)φ (t g) = H_{sQs⁻¹}(t)^{-Wλ} · M_Q(w, λ)φ (g)` for `φ` invariant
  under `U(𝔸)`.
- `eisensteinConjugateParabolicSeries` (module
  `Langlands.Global.AdelicEisensteinConjugateParabolicSeries`) gives
  `E_{sQs⁻¹}(ψ(t⁻¹ ·), μ)(g) = H_{sQs⁻¹}(t)^μ · E_Q(ψ, μ)(g)` for `ψ` invariant under
  `V(𝔸) M'(F)`.

The data for `(P, s Q s⁻¹)` are the same `φ`, `b`, `EP`; the left translates `ψ'_i = ψ_i(t⁻¹ ·)`,
automorphic for the conjugate parabolic by `IsAutomorphicFunctionOn.leftTranslate` and
`parabolicQuotientSubgroup_conjugate`; and the coefficients
`coeff_i λ · H_{sQs⁻¹}(t)^{-Wλ}`, meromorphic since the factor is the exponential of a linear
form (`IsMeromorphicInCoordinatesOn.mul_exp`). The intertwining identity for `s w` follows from
the one for `w` at `t⁻¹ g`. On the patch given by the comparison for `s Q s⁻¹`, regularity of
`Wλ` for `r'` follows from regularity for the conjugated presentation
(`eisensteinRegularityAmbientTransport`, module
`Langlands.Global.AdelicEisensteinRegularityAmbientTransport`), and the `Q`-series are
recovered from the `sQs⁻¹`-series by the second identity at `μ = Wλ`: the factor
`H_{sQs⁻¹}(t)^{Wλ}` cancels the factor `H_{sQs⁻¹}(t)^{-Wλ}` in the coefficients.

## Source

Provenance: derived. J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, take `Q` standard. Every
parabolic is rationally conjugate to a standard one, and this theorem moves the comparison
along such a conjugation.
