# Universal coefficients after a field extension

This internal scalar-extension comparison is used in the proof of Milne,
*Algebraic Groups* (2017), Proposition 4.19, pp. 90–91
(`milne-2017-algebraic-groups`). It applies to arbitrary affine group schemes over
fields, without a reducedness assumption.

The original universal point is lifted to the scalar-extended group on the test
algebra `K ⊗[k] Coord G`. The published pointwise base-change comparison identifies
its matrix with the original universal matrix mapped along the right tensor
inclusion. A ground-field coefficient functional extends to a `K`-linear
functional on this algebra. Testing actual stability at the lifted point
therefore proves preservation under every extended original coefficient.
Closure under the generated operator algebra gives `operator_preserves`.

`extensionHom` is the entrywise extension of coordinate endomorphisms, expressed
as a homomorphism of algebras over the smaller field.
