# Reducedness under algebraic separable base change

This internal helper supports the perfect-field unipotent splitting proof. It proves
that extending a reduced Noetherian algebra by an algebraic separable field extension
preserves reducedness. The proof writes the field as the union of its finitely
generated subalgebras. Each is a finite separable field extension and hence étale;
its tensor product with the given algebra is smooth and reduced. The last assertion
uses the published geometric reducedness of smooth morphisms and Mathlib's flat
geometrically reduced criterion over a reduced Noetherian base.

The mathematical assertion is the algebraic separable-extension ingredient of
Milne, *Algebraic Groups* (2017), Proposition 1.26(a), applied later over a perfect
field. The implemented proof uses the algebraic extension case only.

`isReduced_pullback_of_isAffine` transfers the tensor-product assertion to an
affine reduced locally Noetherian scheme. It identifies the scheme with the
spectrum of its global sections, transports the pullback along that isomorphism,
and uses Mathlib's spectrum-of-tensor-product comparison. Global sections of an
affine locally Noetherian scheme form a Noetherian ring.

`isReduced_pullback` proves the same assertion for every reduced locally
Noetherian scheme by its affine open cover. After pulling back this cover, each
chart is isomorphic to the separable base change of an original affine chart.
Reducedness is local on this open cover. No finite type assumption on the field
extension is required.
