# Division from a Brauer class of full order

`Brauer.isUnit_of_order_eq_reducedDegree` applies Wedderburn–Artin to an actual
central simple algebra \(B\) over \(F\). If \(B \simeq M_r(C)\) for a central
division algebra \(C\), the actual Brauer classes agree and the reduced degrees
satisfy \(\deg B = r \deg C\). When the order of \([B]\) equals \(\deg B\), the
period bound for \(C\) gives \(\deg B \mid \deg C\). Since both reduced degrees
are positive and \(r>0\), this forces \(r=1\). The one-by-one matrix equivalence
transfers the invertibility of every nonzero element of \(C\) back to \(B\).
`Brauer.divisionRingOfOrderEqReducedDegree` equips that same ring with division.

For `FiniteUnitary.isDivisionAt_of_brauer_order`, the supplied chart is an
algebra equivalence from the actual tensor-product completion to \(B\). Tensor
base change preserves the vector-space dimension \(n^2\), so \(B\) has reduced
degree \(n\). The full-period argument gives a unit for each nonzero element
under that equivalence, and its inverse transfers the unit back. The original
algebra carrier can lie in a universe independent of the field universes.
`FiniteUnitary.isDivision_of_isDivisionAbove` chooses a place above the given
real-field place and applies the existing division reflection theorem.

These consequences combine the published Brauer quotient, the determinant
period bound, Wedderburn–Artin and the actual completion interfaces. They
perform the division step after the local invariant computation in Clozel
(1991), Proposition 2.3 and its prescribed-place remark, printed pp. 105–106.
