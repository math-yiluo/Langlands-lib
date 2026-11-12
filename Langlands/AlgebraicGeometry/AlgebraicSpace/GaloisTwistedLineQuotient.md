# The Galois-twisted line as an algebraic space

Author: Worker 105.

This module constructs the algebraic space `X` of Conrad's Example 5.13 (printed p.20): the
quotient `L'/G` of the affine `K'`-line by the étale relation of `GaloisTwistedLine.relation`.
It is support for the proof of `HenselianExtensionPointNotClosedStatement`.

- `lineOver`, `relOver`, `tOver` and `sOver` view the line, the relation and the two
  projections over `Spec K`.
- `space D` is the fppf sheaf quotient `RelationQuotient.quotientSheaf (tOver D) (sOver D)`.
  The construction is exactly as in the Library's proof of Stacks 02WW. The diagonal is
  representable by `hasRepresentableDiagonal_of_isPullback`, using the Library's
  `LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent`.
- `atlas D` is the quotient map from the line.
  - It is étale (`isEtale_of_isPullback`), with the relation as its kernel pair
    (`isPullback_atlas`).
  - It is surjective (`OpenSubfunctorImages.isSurjective_of_isEtale_isLocallySurjective`).

The explicit sheaf quotient is kept, rather than an abstract existence statement, because the
later modules use two of its properties: the kernel-pair square and the local surjectivity of
the quotient map.
