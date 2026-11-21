# Proof of the supercuspidal twist Swan bound reduction

Module `Langlands.Correspondence.HenniartTwistSwanReductionProof` proves the published
[`SupercuspidalTwistSwanBoundReductionStatement`](HenniartTwistSwanReductionStatement.md):

```lean
theorem Langlands.Henniart.supercuspidalTwistSwanBoundReduction :
    Langlands.Henniart.SupercuspidalTwistSwanBoundReductionStatement.{uK, uV}
```

The field universe `uK` and representation-carrier universe `uV` are independent. L0
(existence of normalized levels), L2 (normalized level under a determinant twist), and
T2 (Swan exponent equals rank times level for supercuspidals) are hypotheses, not
conclusions of this proof.

## Implemented proof

1. Fix `π` of rank `n = k + 1`, its given Swan exponent `s`, and a quasicharacter `χ`.
   Apply L0 to the automorphic classes of `π` and `Numerical.supercuspidalCharacterTwist K k χ π`
   to obtain rational levels `x` and `y`. The private lemma
   `supercuspidalToAutomorphic_characterTwist` uses the canonical field and matrix-group
   topologies and `GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist` to identify
   the automorphic class of the latter with the `SmoothDualClass.twist` by `χ ∘ det`
   that occurs in L2.
2. Apply T2 to both supercuspidal classes to obtain finite conductors `c` and `c'`.
   The conductor witness for `HasSupercuspidalSwan K π s` equals `c` by injectivity of
   the coercion into `WithTop ℕ`. Thus T2 gives `(s : ℚ) = n · x`, and the witness
   `s' = c' − n` satisfies `HasSupercuspidalSwan` for the twist and `(s' : ℚ) = n · y`.
   The conductor subtractions are performed in `ℕ` before coercing to `ℚ`.
3. In L2 use `t = Numerical.characterSwanExponent K χ`, definitionally the truncated
   multiplicative conductor minus one. This gives `y ≤ max(x, t)` and equality when
   `x ≠ t`. In `ℚ`, the cast of `max(s, n · t)` is `n · max(x, t)` by the cast laws
   for multiplication and maximum and `mul_max_of_nonneg`. Multiplying L2's inequality
   by the nonnegative rank gives the Swan inequality, which `exact_mod_cast` transfers
   back to `ℕ`. If `s ≠ n · t`, then `x ≠ t`, since `x = t` and `(s : ℚ) = n · x`
   would give `s = n · t`. L2's equality then gives the Swan equality via the same
   maximum identity and cast back to `ℕ`.

## Provenance

This is the final deduction in the operator note *The numerical local Langlands
correspondence for GL_n: counts on the two sides and the recommended route of proof*
(`operator-numerical-llc-route-2026-11-16`, Lemma `lem:level`(ii),
`numerical-LLC-route.tex`, lines 625–627 and 641). It uses the level-to-Swan identity
from part (i), which refers to Proposition `prop:T2` (lines 510–513). The Lean proof
makes explicit the level existence, the comparison of the two twist constructions, and
the passage between natural Swan exponents and rational levels.
