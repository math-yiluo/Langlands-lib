# Invariance of the Eisenstein series

Module `Langlands.Global.RankinSelberg.EqualAnalyticEisensteinInvariance`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

The following identities hold for the Library definitions with no convergence assumption,
because they are identities between the unconditional integrals and sums of the definitions.

- `eisensteinSection_parabolic_mul`: `F(p g) = F(g)` for `p ∈ P'(F)`. The last row of `p g` is
  `a · e_n g` with `a ∈ F^×` (`lastRow_parabolic_mul`), `|det p| = 1`, and the substitution
  `a' ↦ a a'` preserves `d^×a'` (`integral_mul_left_eq_self`) and the weight
  `|a'|^(ns) χ(a')`.
- **`eisensteinSeries_rational_mul`**: `E(γ g) = E(g)` for `γ ∈ GL_n(F)`. Right translation by
  `γ` permutes `P'(F) \ GL_n(F)` (`cosetRightEquiv`), and representatives differ by elements of
  `P'(F)`.
- `eisensteinSection_zeta_mul`, **`eisensteinSeries_zeta_mul`**: `F(a g) = χ(a)⁻¹ F(g)` and
  `E(a g) = χ(a)⁻¹ E(g)` for a scalar idele `a`. Here `|det(a g)|^s = |a|^(ns) |det g|^s`
  (`detPower_zeta_mul`), `e_n a g = a e_n g` (`lastRow_zeta_mul`), and the weight is
  multiplicative (`sectionWeight_mul`, `sectionWeight_one`, `detPower_one_mul`).
- `rationalPoint_mul`, `eisensteinSectionIntegrand_eq'` are auxiliary.

## Provenance

Cogdell 2004, §2.3, printed p.209: "under the center the Eisenstein series transforms by the
central character `η⁻¹`". Invariance under `GL_n(F)` is built into the definition as a sum
over cosets. The proofs are internal.
