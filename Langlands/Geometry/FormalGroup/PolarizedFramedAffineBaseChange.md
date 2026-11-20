# Base change of affine polarized framed triples

`PolarizedFramedAffinePoint.baseChange` pulls back the polarized
target of an affine triple along an actual map of Nilp test algebras.
The framing section pulls back along the induced map of quotient
algebras. Its source is identified with the fixed frame extended to
the new quotient. Its target is identified with the reduction of
the extended polarized target.

The comparisons are polarized order isometries. The source
comparison uses naturality of the residue coefficient map and the
identity comparison. The target comparison uses the commuting
square of the coefficient map and the two quotient maps. Section
composition commutes with pullback and with transport through these
comparisons, so the new framing commutes with the order action.
An integral numerator witnessing the original multiplier pulls back
and is carried through the same isometries. It therefore witnesses
the same \(p\)-adic multiplier for the new framing.

`PolarizedFramedAffinePoint.Iso.baseChange` extends the target
isometry and proves the new framing square by naturality of the
target comparison. These constructions apply to the general affine
polarized triples of `PolarizedFramedAffinePoints`, which encode the
polarized framing conditions in Harris (1997), Appendix, printed
p. 113, and Rapoport–Zink (1996), Definition 3.21.
