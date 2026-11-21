# The full principal adelic quotient with its positive split centre retained

Let `F` be a number field and `G` an affine, locally finite type connected
reductive group scheme over `F`. Write `A_G` for `canonicalSubgroup F G`,
`N` for `AdelicGroupPoints.normOneSubgroup F G`, and `[G]` for
`CanonicalQuotient F G`. The two quotient types in
`principalQuotientProductHomeomorph` are different: the domain divides
out by the actual rational image `G(F)`, whereas the second target factor
`[G]` divides out by `A_G G(F)`. The homeomorphism and its measurable
version `principalQuotientProductEquiv` send the class of `a * n`, for
`a ∈ A_G` and `n ∈ N`, to `(a, [n])`. The second projection on the class
of any representative `g` is its class in `[G]`.

## Construction

`positiveCentreEquiv` maps the intrinsic positive points of the central split
torus to their **actual subgroup** in the adelic points. For its inverse the
construction uses the existing positive projection. The injection and
finite-index range of rational character restriction follow from
`centralSplitTorusCharacter`. The construction chooses a finite splitting
internally; callers do not supply coordinates, a complement or a projection.
The restricted actual logarithm `positiveCentreLogEquiv` is a continuous
multiplicative equivalence from `A_G` onto the ambient real character dual
with addition written multiplicatively. Its value is `characterLogHom`
of the underlying adelic point.
`intrinsicNormOneDecomposition` is the actual multiplication chart of the
intrinsic positive points and the norm-one subgroup. Its principal subgroup
law uses the product formula: a rational point lies in `N`, hence its positive
coordinate is one, and the second factor belongs to the rational image in `N`.

The generic `LeftCosetSpace.productHomeomorph` for this multiplication chart
first gives the product with the norm-one principal quotient. On the two
factors the construction then uses `positiveCentreEquiv` and
`canonicalNormOneQuotientHomeomorph`. The latter homeomorphism sends the
norm-one quotient to `[G]` by inclusion of representatives. The measurable
version uses the existing Borel structures, including the Borel identification
of the inherited quotient sigma algebra on `[G]`.

## Normalization

`intrinsicCentreHaarMeasure` is the Library's sigma-finite intrinsic positive
Haar normalization. Its product with the existing norm-one Haar is sent by
`intrinsicNormOneDecomposition` to the existing ambient Haar, by
`measurePreserving_normOneDecomposition_intrinsic`. This normalization is
independent of the internal choice of a finite splitting. The new measure
`positiveCentreHaarMeasure` is its pushforward to `A_G` by
`positiveCentreEquiv`; the file proves it is Haar. On the second factor,
`canonicalMeasure` is already defined as the pushforward of the existing
norm-one principal quotient measure by inclusion. The exact product pushforward
on the full principal quotient is a separate proposition.

## Source and scope

Getz–Hahn, *An Introduction to Automorphic Representations* (Springer,
2024), §2.6, pp. 68–69 (PDF pp. 85–86), (2.19)–(2.22) and Lemma 2.6.2,
use the common norm-one kernel, the positive split centre and the product
of the two. Equations (2.21) and (2.22) identify `[G]` with the norm-one
principal quotient. The construction here is derived: it retains the
positive factor in the quotient by `G(F)` alone and uses the Library's
fixed ambient and norm-one Haar, not a numerical Haar normalization claimed
from the book. This is the geometric and normalization input to the L3
comparison of the full and relative wave-packet models. It neither
constructs an Eisenstein series nor proves a spectral assertion.
