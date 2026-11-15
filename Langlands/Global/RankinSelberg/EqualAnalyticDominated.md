# Rapidly decreasing majorants of Schwartz–Bruhat functions

Module `Langlands.Global.RankinSelberg.EqualAnalyticDominated`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

## Provenance

Internal. The definition `IsRowDominated` is an encoding chosen for the proof of
`EqualAnalyticStatement`. It is the property of Schwartz–Bruhat functions that the summation
arguments use.

## Declarations

- `IsRowDominated F n Φ`: there is a nonzero `d ∈ 𝒪` such that `Φ x ≠ 0` implies
  `d · x_{j,f} ∈ Ô` for every `j`. Moreover, for every `N` there is `C` with
  `(1 + ‖x_∞‖)^N ‖Φ x‖ ≤ C`, where `x_∞ = archimedeanCoordinates F n x` with the sup norm.
- `isRowDominated_zero`, `IsRowDominated.add`, `IsRowDominated.smul`: closure properties; for a sum
  take the product of the two denominators.
- `continuous_archimedeanCoordinates`, `continuous_finiteCoordinates`.
- `SchwartzMap.exists_one_add_pow_mul_le`: a Schwartz function satisfies
  `(1 + ‖e‖)^N ‖f e‖ ≤ C`.
- `isPureSchwartzBruhat_properties`: a pure tensor `Φ_∞(x_∞) Φ_f(x_f)` is continuous, integrable for
  `rectangleMeasure F 1 n` (`integrable_rect_tensor`) and dominated. The denominator `d` comes
  from the compact support of `Φ_f` (`exists_integer_mul_mem_of_isCompact`). The decay comes from
  the Schwartz bound times a bound for `Φ_f`.
- `schwartzBruhat_properties`: every `Φ ∈ schwartzBruhat F n` is continuous, integrable and
  dominated, by induction on the span.
