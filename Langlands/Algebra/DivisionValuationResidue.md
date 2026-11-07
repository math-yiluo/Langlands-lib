# Residue division ring of a valued division ring

Let `D` be a division ring and let `v : Valuation D Γ₀`, with `Γ₀` a linearly
ordered commutative group with zero. The carriers have independent arbitrary
universes. No commutativity, discreteness, nontriviality of the valuation,
completeness, topology, or characteristic assumption is imposed.

All declarations are in `Langlands.DivisionValuation`. The integer subring is
Mathlib's actual `v.integer = {x : D | v x ≤ 1}`. Define

```
strictIdeal v = {x : v.integer | v (x : D) < 1}
Residue v = v.integer ⧸ strictIdeal v.
```

The first set is an actual ideal of the integer subring, and
`strictIdeal_isTwoSided` proves closure under right multiplication as well.
`strictIdeal_isMaximal` proves maximality among all left ideals. Consequently
`residueDivisionRing` equips the displayed quotient with a `DivisionRing`
structure whose addition and multiplication are the quotient operations.
This construction does not assume that the residue is commutative.

The ring homomorphism `reduction v` is the actual quotient map. It is
surjective and has the following exact tests:

- `reduction v x = 0` if and only if `v (x : D) < 1`;
- `reduction v x ≠ 0` if and only if `v (x : D) = 1`;
- `reduction v x = reduction v y` if and only if
  `v ((x : D) - (y : D)) < 1`.

`reduction_units_surjective` proves that the induced map on unit groups is
surjective. `reduction_unit_eq_one_iff` identifies its kernel by
`v ((u.val : D) - 1) < 1`. These refer to units of the original integer
subring and its actual residue division ring.

## Implemented proofs and provenance

This is an internal consequence of Mathlib's valuation, integer-subring,
ideal and quotient constructions. It fills the noncommutative case: the
existing `Valuation.Integers` unit criterion is formulated for commutative
rings, so the proof below works directly with the integer subring.

`isUnit_iff_value_eq_one` proves that an integral element is invertible in
that subring exactly when its value is one. For an integral unit `u`, both
`u` and its inverse have value at most one, while the product of their
values is one. Hence the value of `u` is one. Conversely, an element of
value one is nonzero in `D`; its inverse in `D` also has value one by
`Valuation.map_inv`, so both elements define a unit of `v.integer`.

The strict-value ideal is closed under addition by the valuation maximum
inequality. Multiplying an element of value less than one by any integral
element preserves that strict inequality on either side. Commutativity of
the value group, rather than of `D`, supplies right closure.
`mem_strictIdeal_iff_not_isUnit` then identifies this ideal with the nonunits.
It is proper because it omits one. A left ideal containing an element
outside it contains a unit, hence contains one. This proves maximality as
a left ideal. The same unit argument proves
`le_strictIdeal_of_ne_top`: every proper left ideal lies in it.

Mathlib's `Ideal.Quotient.divisionRing` applies to the proved two-sided ideal
that is maximal as a left ideal. The reduction tests follow from quotient
membership, the valuation bound for integral elements, and the identity
`f x = f y ↔ f (x - y) = 0` for a ring homomorphism. To lift a residue unit,
choose an integral representative by quotient surjectivity. Its nonzero
residue forces its value to be one, so the unit criterion provides an
integral unit with the required image. Finally, equality to one in the
unit group is equality of its underlying residue elements, to which the
difference test applies.

## Scope

The construction applies in particular to the canonical reduced-norm
valuation on a local central division algebra. This module is general and
does not identify that specialization, prove finiteness or commutativity of
its residue, construct a cyclic maximal subfield, or prove local SK1 or the
local Kneser–Tits proposition. Those arithmetic and structural conclusions
remain separate obligations.
