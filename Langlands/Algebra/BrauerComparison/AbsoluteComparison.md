# The Brauer group and the continuous cohomology of separable-closure units

An actual central simple algebra has a finite Galois matrix splitting in
its ground field's universe. This splitting field embeds into any chosen
separable closure and its image lies in a finite Galois intermediate
field. Extending the matrix chart to that field gives a chart in the
chosen closure. `csaContinuousClass` inflates the relative class of this
chart to Mathlib's continuous degree-two cohomology of the closure's
discrete units.

Two finite stages lie in their finite Galois compositum. After extending
the charts to the compositum, compatibility of the relative class with
inflation and independence of the matrix chart show that their continuous
classes agree. The computation also applies to an abstract finite Galois
splitting field with any specified compatible embedding into the closure.
The relative class is invariant under matrix-stable equivalence and is
additive under the tensor product, so `brauerContinuousHom` passes to the
actual Mathlib Brauer quotient and respects its addition.

If an algebra's continuous class is zero, injectivity of finite relative
inflation makes its relative class zero in its chosen splitting field.
The matrix descent splitting criterion yields a split matrix algebra over
the ground field, hence a zero Brauer class. Conversely every continuous
class has a finite Galois representative. The projective regular matrices
of a representing unit cocycle descend to a central simple algebra whose
relative class is that representative. This gives `brauerContinuousEquiv`
for an arbitrary separable closure and `brauerEquiv` for Mathlib's chosen
separable closure. The multiplication of factor sets under tensor product
corresponds to addition, the opposite algebra gives the negative class,
and a split matrix algebra has class zero.

The sign is the descent/PGL sign of J.-P. Serre, *Local Fields* (1979),
Chapter X, §5, printed pp. 158–159. The implemented route uses directly
the scalar `P_s s(P_t) P_(s*t)⁻¹`; the regular descent starts with that
same factor set. The constructions apply to every field, including
imperfect fields, and each field and algebra can be in any common universe.
