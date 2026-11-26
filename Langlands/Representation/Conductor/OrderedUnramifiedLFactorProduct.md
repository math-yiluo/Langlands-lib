# `L(s, π × I(x)) = ∏_j L(s, π × χ_(x_j))` from the premises

Module `Langlands.Representation.Conductor.OrderedUnramifiedLFactorProduct`, namespace
`Langlands.Conductor.OrderedUnramifiedTemperedType`, over a nonarchimedean local field `F`.

## Contents

- `isPadicPairLPolynomial_congr_whittakerSets`,
  `isPadicSymmetricLPolynomial_congr_whittakerSets`: the all-field L-polynomial relations
  depend only on the Whittaker functions of the two members, for `ψ` and `ψ⁻¹`. These are
  the all-field forms of the Library's p-adic lemmas of the same names (module
  `GenericLanglandsQuotientLFactorProof`) and rest on the published field-generic
  `RankinSelberg.isPairLPolynomial_congr_whittakerSets` (JPSS 1983, Remark (3.3): the
  L-factor depends only on the Whittaker models).
- `lPolynomial_principalSeries_eq_prod`: assume over `F`
  `GenericStandardModuleStatement F`, `TemperedPoleBoundStatement F` and
  `InducedTailLFactorAt F` (for the two universe orders used). Let `π` be generic on
  `GL_(n+2)(F)` and `|x_1| ≤ ⋯ ≤ |x_(n+1)|`. If `PI` is the certified L-polynomial of
  `(π, I(x))` and `Pi j` that of `(π, χ_(x_j))`, then `PI = ∏ j, Pi j`.

## Proof of `lPolynomial_principalSeries_eq_prod`

1. The classification premise gives a datum `d` whose standard module `ξ` has the
   Whittaker functions of `π`, so `PI` is the L-polynomial of `(ξ, I(x))` and `Pi j` that
   of `(ξ, χ_(x_j))` (Whittaker-set congruence).
2. `I(x)` is the standard module of `unramifiedDatum`, and `χ_(x_j)` that of the one-block
   `pointDatum`. The all-field (9.4)(3), `temperedTypeLPolynomial_product`, gives
   `PI = ∏_i ∏_j Q i j` with `Q i j` the polynomial of the twisted blocks
   `(τ_i ν^(u_i), χ_(x_j))`, and `Pi j = ∏_i Q i j` (the twisted block of `pointDatum` is
   the `j`-th twisted block of `unramifiedDatum`).
3. Exchanging the two products gives `PI = ∏ j, Pi j`.

Source: JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), (9.4), displays (3) and (4),
printed page 458; Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`),
printed page 519, where this identity underlies Lemma 3.
