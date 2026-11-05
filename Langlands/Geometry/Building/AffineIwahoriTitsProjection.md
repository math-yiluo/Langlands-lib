# The actual affine Tits projection and its kernel

This internal unit develops the subgroup algebra for the actual datum in
`AffineIwahoriTits.lean`. It is derived from the published definitions and the
quotient lemmas in `IwahoriWeylQuotientLemmas.lean`. Its source context is
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Definition 2.6.23,
Definition 7.4.1 and Theorem 7.5.3(1),(2), with the corrected saturation convention
already present in the fixed datum. It proves no saturation claim.

`centralizerZeroInZero` is the image of the supplied actual `Z(F)^0` in `G(F)^0`.
It is defined by restricting its image in `G(F)` to `P.zeroSubgroup`. The
published definition of `P.zeroSubgroup` already contains that image, so mapping
this restriction back into `G(F)` recovers the full image. The image lies in the
actual normalizer and in every restricted generated parahoric.

Assuming only normality of `P.normalizerZero` in the full normalizer, the literal
`P.affineTitsProjection` is surjective: it is the composite of the subtype-swapping
multiplicative equivalence and the surjective quotient map `P.affinePartMk`.
The quotient identity criterion identifies its kernel with
`P.centralizerZeroInZero.subgroupOf P.normalizerInZero`. Thus the projection
kernel lies in every `P.parahoricInZero Ω`, even before any assertion that the
full generated parahoric lies in `G(F)^0`.

The lemma `affineTitsProjection_ker_eq_iff` identifies the remaining Tits kernel
condition with the geometric intersection equality
`P.parahoricInZero Ω ⊓ P.normalizerInZero = P.centralizerZeroInZero`. This is an
equivalence of the two obligations; it does not prove that equality.

Finally, an `IsAffineWeylComparison` acts on the literal Tits projection by the
actual apartment action. Two comparisons satisfying that predicate are equal:
every element of the actual affine part has an actual restricted-normalizer
representative, and compatibility fixes their values on each representative.
No existence of such a comparison, zero-subgroup normality, full parahoric
containment, Tits multiplication, or Tits saturation is assumed or proved here.
