# Localizing a supplied simultaneous standard basis

This internal structural consequence permits analytic consumers to work
with a compact open structural subgroup while retaining the original
supplied `SimultaneousStandardBasisAt` property.

`normalBasisBelow B L` is the subfamily of `B` consisting of the
subgroups contained in `L`. If `B` is a compact open normal identity
basis relative to `K0`, and `L` is an open subgroup contained in `K0`,
`CompactOpenNormalBasis.restrict_below` proves that this subfamily is a
compact open normal identity basis relative to `L`. Normality follows
by restricting the normalizer containment from `K0` to `L`. Cofinality
follows by applying the original neighborhood basis to the intersection
of the desired neighborhood with the open subgroup `L`.

For the actual simultaneous standard basis,
`SimultaneousStandardBasisAt.exists_compactOpen_le` chooses a compact
open member `L` of the supplied basis inside any specified ambient open
subgroup `H`. It gives `L ≤ H`, `L ≤ K0`, and the same simultaneous
standard basis property at `L`.

Restrict the original basis to `normalBasisBelow B L`. Its intersections
with each closed actual standard Levi form the required inherited
basis by `CompactOpenNormalBasis.inherited`. The original compatible
split components and every original parabolic basis-member property
apply to the smaller family without alteration.

No compactness or openness of the original `K0` is asserted or needed.
The result supplies no Cartan covering or Iwasawa decomposition. Those
remain separate structural obligations of analytic consumers.
