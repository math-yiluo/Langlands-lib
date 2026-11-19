# The valuation quotient of the split local similitude group

`splitValuationCoordinates` assigns two integer orders to an actual
split similitude. They are the order of the opposite unit in the
original division algebra and the order of the multiplier in the
scalar field. The integer orders are written multiplicatively
in the group homomorphism. `localSplitValuationCoordinates` uses
the Library's reduced-norm valuation over the center `F` and the
canonical valuation of the scalar field `k`.

The common kernel consists of the elements on which both
multiplicative valuations have value one. `ValuationComponentGroup`
is the group quotient by this kernel. Given an explicit unit of
order one in each factor, `valuationComponentEquiv` identifies
this quotient with the product of two copies of `ℤ`. It uses
integer powers of those units as a right inverse of the order map.

Under those normalizations, the Weil right translation adds `1`
to the opposite-unit order and `f` to the multiplier order.
The determinant correction adds `-detOrder` to the opposite-unit
order and preserves the multiplier order. These formulas follow by
applying the orders to the split component elements.

The source is Harris 1997, Appendix, printed pp. 113–115
(PDF pages 39–41), concerning the character lattice and the
translations in (A.2), (A.3) and (A.6). The module constructs the
quotient for the two displayed valuations. Identifying their
common kernel with the full rational-character kernel `C_p` of
(A.2) and identifying it with the connected components of the
formal moduli space remain separate comparisons.
