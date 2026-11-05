# Three-factor Haar balance for equal dynamic centralizers

Author: Worker 700.

This internal deduction concerns two cocharacters of the same split torus in a
smooth affine group scheme over an arbitrary nonarchimedean local field. The
torus map `i : T.toGrp ⟶ G` has monomorphic underlying scheme map
(`Mono i.hom.hom.left`), and both Haar square theorems assume
`hroot : HasRelativeRootSystem i`. Their dynamic centralizers must agree as
complete subgroup functors. The acting affine
group `Z` maps into that common centralizer and contains the displayed torus
through a factorization `j`. The represented radical groups `U` and `V` and their
literal intersection `C` have finite Lie coordinates. The ambient rational-point
group has the canonical point topology, and its local compactness,
nonarchimedean group structure and Hausdorffness are explicit hypotheses. The
three rational subgroups are assumed closed, as required by their Haar
characters.

`centralizingHaarCharacter_product_square_of_centralizer_eq` proves that the
product of the forward conjugation Haar characters of `U` and `V` equals the
square of the forward Haar character of `C`, on all rational points of `Z`.
`centralizingHaarCharacter_values_square_of_centralizer_eq` evaluates this
identity in the nonnegative real numbers. In addition to the root-system and
other hypotheses above, both declarations explicitly assume
`Function.Injective (characterRestrict j)`. Neither proves that hypothesis.

The proof uses the three-factor rational determinant equality
`Dynamic.rationalCharacterEval_centralizingDeterminant_square_of_centralizer_eq`
from `EqualCentralizerDeterminantBalance`, retaining `hroot`. This relative
root-system hypothesis supplies the opposite-weight multiplicity symmetry used
by the underlying dimension-weighted determinant balance. The published
`smoothAffineCentralizingUnipotentHaarDeterminant` identifies each full-radical
Haar factor with the absolute value of its actual conjugation determinant.
`unipotentIntersectionHaarDeterminant` does the same for the literal common
intersection. The required cocharacter centralization follows from equality of
centralizers and `Dynamic.range_le_centralizer`. Multiplicativity of
`MeasureTheory.distribHaarChar` then transports the determinant equality to Haar
values. Extensionality of units and monoid homomorphisms gives the character
identity.

These Haar characters are the existing `centralizingUnipotentHaarCharacter` and
`centralizingUnipotentIntersectionHaarCharacter`; their definitions use
`HaarModulus.closedNormalizerCharacter` of the original ambient rational-point
group, composed with the original acting-point map. Thus the factors retain the
published forward-conjugation convention. This module supplies no conjugation
transport or specialization to standard parabolics, and it does not prove the
unconditional rational corrected-orbit target. Discharging restriction
injectivity and identifying the literal transported standard subgroups remain
separate requirements for that application.

The deduction has derived provenance from the exact declarations named above.
It introduces no external structural assumption beyond its displayed hypotheses.
