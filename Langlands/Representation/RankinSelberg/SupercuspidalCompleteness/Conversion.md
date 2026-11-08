# Compact Whittaker test functions as Gelfand–Graev vectors

Internal helper module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`.

- `toWhittaker ψ n : GelfandGraevFunctions ψ n →ₗ[ℂ] WhittakerFunctions ψ n` sends a vector of
  `gelfandGraev ψ n = c-Ind_N^G ψ` to its underlying function. The compact-induction covariance
  `f(u g) = ψ_N(u) • f(g)` is exactly the `standardCharacter` equivariance of `WhittakerFunctions`.
- Basic properties:
  - `toWhittaker_apply` evaluates the map.
  - `toWhittaker_injective` says the map is injective.
  - `toWhittaker_translate` says it commutes with right translation.
- `exists_toWhittaker_eq`: every `H` satisfying `IsCompactWhittakerTestFunction ψ n H` is
  `toWhittaker ψ n f` for some Gelfand–Graev vector `f`.
  - The open subgroup in the hypothesis provides the uniform right stabilizer.
  - The support condition `H(g) ≠ 0 → g ∈ N C` with `C` compact places the projected support in
    the image of `C` in `N \ G`.
  - That projected support is closed (`isClosed_quotientSupport` from `CompactGrading`), hence
    compact.
