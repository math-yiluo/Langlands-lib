# Finite invariant affine covers from an étale scheme quotient

This is derived scheme and pullback infrastructure for the finite symmetric-tuple
filtration in Stacks Project Lemmas 68.8.6 (Tag 07ST) and 68.8.3 (Tag 0BBN).
Those sources supply the intended compact invariant opens and their étale
scheme covers. The construction here applies to any actual étale morphism
whose kernel pair is a supplied étale equivalence relation. It does not assume
Noetherian approximation.

`InvariantAffineQuotientCover E` stores a finite index type, an open cover of
`E.U` by invariant affine opens, and the affine quotient property of every
induced open-chart relation.

For `f : E.U → M` and a categorical pullback square identifying `E.R`
with the kernel pair of `f`, `isInvariantOpen_preimage_of_kernelPair` proves that
the inverse image of any open of `M` is invariant, by taking inverse images in
the commuting square.

`isPullback_chart_morphismRestrict` proves the full kernel-pair universal
property after restricting `f` to an open `V` of `M`. Commutativity follows
after composing with the open immersion of `V`. Given two maps into the
inverse-image open with equal composites to `V`, the original pullback supplies
their arrow in `E.R`, and `Chart.lift` lifts both endpoints. Endpoint
extensionality of the chart relation proves uniqueness.

`surjective_morphismRestrict_of_subset_range` proves that the restriction is
surjective if `V` is contained in the image of `f`. A point of `V` has a preimage
under `f`, which belongs to the inverse-image open; injectivity of the open
immersion verifies its image under the restricted morphism.

`hasAffineQuotient_chart_morphismRestrict` uses these two results when `f`
is étale and `V` is affine. The restricted map is étale by base change and
hence flat and locally of finite presentation. With its proved surjectivity
and kernel pair, it is an actual witness to the published affine quotient
predicate.

`invariantAffineQuotientCoverOfCompactImage` assumes that `E.U` and `M` are
affine, that `f` is étale with the given kernel pair, and that its image is a
compact open `W`. Mathlib's affine-open basis and finite-subcover theorem give
a finite collection of affine opens whose union is `W`. Pulling them back
along `f` gives affine opens covering `E.U`, since `f` is an affine morphism.
The preceding lemmas prove their invariance and affine chart quotients.
Each chosen target open lies in `W`, which supplies the needed surjectivity.

`InvariantAffineQuotientCover.descend` applies the published common-level
quotient-cover descent construction to this package in a supplied cofiltered
cartesian diagram of affine relations with its object limit. It retains all
the package's opens as inverse images at one level and retains their affine
quotient properties. It neither glues the chart quotients nor constructs a
Noetherian approximation.
