# The finite regular representation detects the order obstruction

For a finite abstract group `G` over a field `k`, its regular representation on
the functions `G → k` is semisimple if and only if `(Nat.card G : k) ≠ 0`.
In characteristic `p` this is equivalent to `¬ p ∣ Nat.card G`.
The function representation is reused from Mathlib's
`TannakaDuality.FiniteGroup.leftRegular`, with action
`(g · f)(t) = f(g⁻¹t)`. As in that definition, `k` and `G` share a universe.

The auxiliary construction `fixedSubrepresentation` bundles the fixed vectors
of any linear representation as a subrepresentation. It permits independent
universes for the coefficient ring, group, and module.

For necessity, semisimplicity gives an equivariant projection onto the fixed
vectors. All the coordinate basis vectors are translates of the basis vector
at the identity, so their projections agree. Their sum is the constant
function with value one. The projection fixes this function, whereas the sum
of their projections is zero if the group order vanishes in `k`.
Evaluating at the identity gives a contradiction. Sufficiency is Mathlib's
Maschke theorem. The characteristic-`p` form uses the defining vanishing
criterion for the natural-number map to a field of characteristic `p`.

This is internal finite-group infrastructure for the prime-to-characteristic
component-order condition in Nagata's theorem, stated in J. S. Milne,
*Algebraic Groups*, corrected reprint (2022), Remark 12.56, printed p.249.
The implemented elementary regular-representation proof is explained above;
Milne does not supply it in that remark. The official errata snapshot of
4 November 2026 contains no correction to this passage.
Realizing this regular representation as a representation of a finite
group-scheme quotient remains a separate obligation.
