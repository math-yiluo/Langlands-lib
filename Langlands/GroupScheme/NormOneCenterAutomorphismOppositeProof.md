# Centre-moving norm-one automorphisms force an opposite-algebra equivalence

`Langlands.GroupScheme.normOneCenterAutomorphismOpposite` proves the exact
published `NormOneCenterAutomorphismOppositeStatement` at every universe `u`.
The target and its imported Lean/Markdown pairs are retained unchanged.

For a finite-dimensional central simple algebra over a field, choose the
published finite Galois splitting field and its actual matrix-algebra chart.
The centre-fixation reflection theorem shows that the original centre-moving
automorphism remains centre-moving after field extension. Transport along the
published actual norm-one/special-linear scheme isomorphism gives a centre-moving
split special-linear automorphism.

The split outer-matrix construction first moves the image of the pinned maximal
split torus back by a rational inner automorphism. The published torus-compatible
classification then applies. Matrix conjugation fixes the full centre on every
test scheme, so centre movement selects the inverse-transpose case. Removing the
inner correction gives one outer matrix over the splitting field. The affine
splitting comparison converts its all-test formula to the original tensor-unit
coordinates.

The actual group-scheme automorphism induces an affine coefficient automorphism
that commutes with every coefficient Galois automorphism, by naturality of
relative affine points. The supplied outer formula defines a conjugated-transpose
algebra anti-equivalence over the splitting field. Norm-one units span that
matrix algebra, so Galois covariance extends from the units to the entire
algebra. Fixed-tensor descent then produces a scalar-fixing algebra equivalence
from the original algebra to its opposite.

The implementation assembles these internally derived helpers with
`NormOneOuterDescent.oppositeEquivOfOuter`. It imposes no additional premise on
the field, characteristic or reduced degree, and no division-ring or
involutivity hypothesis. The full scheme-theoretic centre is retained on every
test scheme, including nonreduced schemes. The proof does not use the local
rank-one Tits index or classification statements or local Kneser–Tits.

The provenance is internal: this is the structural implication isolated by the
published target. The proof uses the published split automorphism, central-simple
splitting and matrix-span results rather than asserting a new attribution to
external literature.
