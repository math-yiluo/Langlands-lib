# Swan exponents and upper breaks of irreducible Weil classes

This module bridges the natural exponent in `HasWeilSwan` to the real upper
break in `VirtualRepresentation.LocalWeil.Ramification.lastBreak`. This is an
internal proof step for the integer conductor-count step: Henniart (1988),
Corollaire 1.4 and §3.4, use the ratio of the Swan conductor to the rank as the
slope. The unit proves the comparison for the actual Library representations
and conductors, not the conductor-count step.

## Implemented proof

1. `irreducible_presentation_swan_eq_rank_mul_lastBreak`: let `t` be the last
   break, and choose an upper endpoint for the integral at least as large as
   `t` and the finite presentation's upper cutoff. The Library writes the Swan
   sum as the integral of the upper fixed-space codimension. Via
   `presentationUpperFixedComparison`, the codimension is the full rank on
   `(0,t)` and zero above `t`, by the positive threshold theorem for
   continuous irreducible Weil representations. Split the integral at `t` and
   integrate the constants on the two open intervals.
2. `irreducible_artin_sub_rank_eq_rank_mul_lastBreak`: the Artin sum is the Swan
   sum plus the inertia-fixed codimension. If `t > 0`, the fixed space at `t`
   is zero, hence so is the fixed space at upper index zero by monotonicity.
   Subtracting the rank then subtracts exactly the tame codimension. If
   `t = 0`, the Swan sum is zero and the Artin sum is at most the rank, so
   truncated natural subtraction correctly yields zero in this case too.
3. `weilSwanExponent` is an internal choice of the natural Swan exponent:
   choose the natural Artin conductor by the published existence theorem and
   subtract the rank. The comparison just proved makes the result independent
   of the presentation and representative. More precisely,
   `hasWeilSwan_iff_eq_rank_mul_lastBreak` says `HasWeilSwan K σ s` holds exactly
   when the real cast of `s` is the rank times the last break of any actual
   representative of `σ`. The forward direction uses the presentation in the
   hypothesis and the published intrinsic class break label. The reverse
   direction compares the proposed natural number with `weilSwanExponent` by
   injectivity of the natural cast into the reals.
4. `lastBreak_le_iff_isTrivialAbove` uses the published strict threshold at
   positive indices; the converse takes strict bounds at `b + ε` for every
   positive real `ε`. In particular a weak bound by `b ≥ 0` checks triviality
   at **every** real index strictly greater than `b`, not just at a next
   integer.

The field and representation-carrier universes are independent. This module
requires irreducibility and continuity for the single-break conductor formula;
no single-break formula for an arbitrary reducible representation is asserted.
