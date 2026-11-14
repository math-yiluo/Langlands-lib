# Unipotence of bilinear coordinate groups

This derived supporting construction concerns the bilinear coordinate group
`(a,b)(a',b') = (a+a', b+b'+form c a a')` from
`BilinearCoordinateGroup`. Over any field and with any finite index type,
it proves unipotence in the Library's coefficient-representation sense.
No restriction on characteristic or on the bilinear form is required.

The vector coordinate functions are primitive. The published primitive
polynomial quotient API constructs their homomorphism to the standard
vector group. The remaining polynomial variable is the scalar coordinate;
this proves that the projection is flat and surjective. Its actual
scheme-theoretic kernel has natural scalar coordinates on every scheme
test, since a point is in this kernel precisely when its vector coordinate
vanishes. The bilinear correction then vanishes, so the kernel is the
additive line as a group scheme. Its unipotence and that of the vector
quotient imply unipotence of the bilinear group by the published affine
extension theorem.

The provenance is the bilinear group law (C.4.2) and the kernel argument in
Kaletha–Prasad (2023), Appendix C.4, printed pp.700–702 / PDF pp.731–733,
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
This is a derived general unipotence argument for the coordinate groups;
it does not identify any unitary integral model or its special fibre.
