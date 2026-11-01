# Actual Aubert images on segment induction support

Author: Worker 165.

This is an internal derivation on the genuine exact finite-length
Grothendieck group and its proved composition-factor lattice. It applies
to every actual irreducible subquotient of the increasing induction
of a positive-length segment from a positive-rank supercuspidal base.
The supplied p-adic field and topology, independent field and carrier
universes, and saturated representation carriers remain arbitrary.

`segmentInductionAubert_effective` proves that multiplying the Aubert image
by `(-1)^(m*r-m)` gives an effective factor vector. The support theorem for
quasicuspidal induction first confines the unadjusted image to the original
induction's support; scalar multiplication preserves that containment.
Hereditary quasicuspidality of the uniform Jacquet object lets actual reversed
Jacquet exchange compute the Jacquet image of this signed vector as the
positive factor vector of an actual transported Jacquet object. The two
signs multiply to one. Segment Jacquet detection then reflects this
effectivity to the original supported vector.

`SegmentInductionAubertImageStatement` asserts an actual irreducible
Aubert image up to sign for each such actual irreducible subquotient.
`segmentInductionAubertImage` proves it. Induction commutation and the
quasicuspidal eigenvalue make the same signed operator fix the full
induction class. Aubert involutivity gives injectivity. The preceding
effectivity result supplies the positivity premise of the generic
actual fixed-factor-vector theorem. Positive integral counting then
forces the image of each supported generator to be one generator;
realization gives an actual irreducible representation with the displayed
class equality up to sign.

The substantial inputs are actual exact normalized induction and Jacquet
class maps, their compatibility with Aubert's unadjusted operator,
quasicuspidal geometric filtrations, minimal Jacquet detection, scalar
separation of the segment filtration, the independent involutivity proof,
and positive integral-lattice counting. These inputs and this derivation
retain all actual short exact sequence relations, including nonsplit ones.
No global irreducible-image theorem, classification, exhaustion, or
constituent-existence assertion is assumed or established here.
