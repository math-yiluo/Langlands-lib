# Geometric fibre and coordinate-order transfer for fpqc descent

Internal derivations from the published field predicate, finite Galois
splitting, geometric-fibre comparison and affine tensor-coordinate isomorphisms.

`IsMultiplicativeType.of_fieldExtension` composes a splitting extension with the
original ground-field extension. `IsMultiplicativeType.fieldExtension` takes a
published finite Galois splitting field and embeds it into the algebraic closure
of the new ground field. The field-tower pullback isomorphisms identify the
resulting actual group schemes.

`FpqcMultiplicativeType.coordinateOrder` uses the actual structure morphism of
a scheme over a field to define the scalar action on its global sections. The
value is the natural-number `Module.finrank`; it is zero for infinite-dimensional
coordinate algebras. Isomorphisms over that field preserve the value. Scalar
extension preserves it for affine schemes, by the published tensor-coordinate
isomorphism and the tensor-product dimension theorem.

This module is a helper toward fpqc descent. It does not prove the full
`MultiplicativeTypeFpqcExtensionStatement`.
