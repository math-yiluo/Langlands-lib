# Entire functions plus two simple fractions

Module `Langlands.Global.RankinSelberg.EqualAnalyticPoles`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Let `G` be entire and `f(s) = G(s) + a₁/(m s + b₁) + a₂/(m s + b₂)` with `m ≠ 0`. Let `P` be a
set of complex numbers.

- `hasAtMostSimplePolesIn_entire`: `G` has at most simple poles in any `P` (continuity bounds
  `(s - p) G(s)` near `p`).
- **`hasAtMostSimplePolesIn_two`**: if `-b₁/m, -b₂/m ∈ P`, then `f` is holomorphic off `P`.
  Moreover `(s - p) f(s)` is bounded near every `p`, because
  `a/(m s + b) = (a/m)/(s - (-b/m))` (`frac_eq`) and `|(s - p)/(s - s₀)| ≤ 1` for `s` near `p`
  (`exists_norm_div_le_one`).
- `boundedInVerticalStripsAwayFrom_entire`, **`boundedInVerticalStripsAwayFrom_two`**: if `G`
  is bounded on vertical strips, then so is `f` away from `P`, using
  `|a/(m s + b)| ≤ |a/m|/δ` at distance `≥ δ` from `-b/m`.

The predicates `HasAtMostSimplePolesIn` and `BoundedInVerticalStripsAwayFrom` are the
Library's (`EisensteinStatement`, `EqualAnalyticStatement`).

## Provenance

Elementary complex analysis; the proofs are internal.
