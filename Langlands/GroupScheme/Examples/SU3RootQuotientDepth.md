# Maximal depths in quadratic root-coordinate cosets

Worker 244. This is an internal derivation from the published quadratic parameter
group, its scaling operation, and the inverse-degree lattice theorem for the
base-normalized henselian extension valuation.

The generic lemmas use an actual trace-one scalar of maximal value. Dividing the
second coordinate of a noncentral point by the norm of its first coordinate
gives trace one. Maximality therefore bounds the second-coordinate value by that
of the displayed lift, and halving bounds its root depth. The optimal lift has
the same first coordinate, so their quotient belongs to the literal central
subgroup.

Conjugation invariance of the valuation makes the optimal depth exactly
`ω x + halfTop (ω t)`, where `x` is the nonzero first coordinate and `t` is the
chosen maximal trace-one scalar. The root filtration therefore has a point with
first coordinate `x` at level `r` if and only if `r` is at most this displayed
depth. The forward implication uses the maximal-depth bound, and the reverse
implication uses the displayed lift itself.

For a compatible tower of fields `k → E → L`, assume that `E/k` is finite,
`L/k` is separable, and `L/E` is separable quadratic. Let `v` be an
integer-valued valuation on `k` whose valuation subring is henselian. For the
base-normalized valuation `henselianSeparableAddValuation v hH L`, trace-one
values are at most zero by the valuation inequality and conjugation invariance.
They belong to the inverse total-degree integer lattice. The greatest-element
property of bounded nonempty subsets of the integers therefore supplies a
trace-one scalar of maximal value. Nonemptiness uses the published separable
trace-one construction. No field-characteristic, residue-characteristic or
residue-perfection restriction is imposed.

These results concern the explicit coordinate group. They do not identify it
with the root group of an arbitrary quasi-split group or assert a ramification
description of the jump set.
