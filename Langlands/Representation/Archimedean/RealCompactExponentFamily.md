# Real standard modules with one varying exponent

By `RealExponentDeformation.exists_eqOn`, two real standard modules with the
same parity and weight data have the same restrictions of their finite
vectors to the compact group. `compactEquiv` identifies these realizations
using the unique extension with the specified values on `O(n)`. The right
translation by a compact element stays on the compact group and therefore
commutes with this equivalence.

`IsExponentShift.transportedLie` conjugates the Lie operator to the base
model. On the compact group, `rightDerivative_eq_of_exponent_shift` expresses
its difference from the base operator as multiplication by the parameter
times the diagonal weight of the shift. The difference at parameter one
therefore gives the coefficient of the affine family. The compact restriction
determines the vector, so this gives an equality of operators on the base
model. `isExponentShift_shiftBlock` supplies such a family for a shift of
one block. Its exponent increment is one on the diagonal positions of that
block and zero elsewhere.

This derived compact-picture construction applies the Library's real
exponent deformation formula. It supplies the affine families for comparing
constituents under reordering, as motivated by Badulescu–Renard (2010),
Remark 2.3 and Proposition 2.4, pp. 1123–1124 (PDF pp. 10–11).
