# Ordered distributions on the actual Frobenius-origin quotient

Let `G` be an actual affine group scheme over a field `k : Type u`, let
`p` be the exponential characteristic of `k`, and let `r` be a natural
number. Supply an ordered family of actual homomorphisms `x_i : Ga -> G`
indexed by `Fin d`. The coordinate comparisons below assume that the
canonical `coordinateMap x`, constructed from the actual universal
ordered point, is bijective.

`IsOriginPoint p r A g` is an intrinsic condition on an original affine
point over `A : CommAlgCat.{u} k`: the value of every coordinate in the
actual identity augmentation ideal has zero `p^r`-th power. The theorem
`isOriginPoint_orderedPoint_iff` identifies this condition at the actual
ordered point with `t_i^(p^r) = 0` for every parameter. One direction tests
the inverse image of each polynomial variable under the supplied
coordinate equivalence. The other uses the published characteristic
power identity for polynomial evaluation and preservation of the actual
identity by `coordinateMap`.

`orderedModelEquiv` specializes the existing Frobenius coordinate model to
this particular ordered coordinate equivalence. It identifies the actual
coordinate algebra modulo the Frobenius image of its actual augmentation
ideal with the polynomial quotient by `X_i^(p^r)`. Following it by the
retained coefficient equivalence gives `coordinateCoefficientsEquiv`.
Its value on the quotient of an original coordinate is exactly the
coefficient of that coordinate's canonical ordered pullback.

`coordinateBasis` is the basis supplied by this finite coefficient
equivalence. Its dual `distributionBasis` is a basis of the linear dual
of the actual quotient, indexed by exponents with each entry at most
`p^r - 1`. Evaluation on original quotient coordinates is precisely
extraction of the corresponding ordered coefficient.

For any finite matrix representation of the original `G`,
`distributionAction` applies a quotient functional entrywise to the
original action matrix at the genuine universal quotient point, then
acts on column vectors. The theorem `distributionAction_basis` proves
that each dual basis vector acts as exactly the ordered product of the
restricted additive divided powers. The proof uses evaluation of the
original universal matrix and the exact canonical ordered pullback of
that matrix. Mapping the spanning dual basis proves that the whole
distribution action has the span of these bounded operators as its
linear image.

`originOrbitSpan` uses all scalar contractions of actual
`IsOriginPoint` actions on a specified vector, over every commutative test
algebra in universe `u`. Unique ordered parameters and the intrinsic point
criterion identify it with the previously constructed bounded
nilpotent-tuple orbit span. The published coefficient expansion and
extraction result then identify this span with the span of the bounded
ordered divided-power images of that vector. All these comparisons
retain nonreduced and zero test algebras and require no infinitude or
perfection assumption on the field.

This unit is derived from the Library's actual ordered coordinate,
Frobenius quotient, polynomial coefficient and divided-power interfaces.
It supplies a basis of the actual quotient dual; it does not assert
linear independence of that basis's images in a particular
representation. It does not construct a multiplication on the quotient
dual or a group scheme Frobenius kernel. Existence of the required
bijective ordered coordinate map, existence of root subgroups, comparison
with an entire induced representation, and the host Steinberg big-cell
statement remain separate obligations.
