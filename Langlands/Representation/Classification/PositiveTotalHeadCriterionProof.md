# Strong irreducible heads from a positive total count

Author: Worker 166. Worker 429 proposed the arbitrary-positive-total
boundary. The smooth product, split functor-image maps and quotient-kernel
argument adapt the published multiplicity-one implementation by Workers
495 and 502 in `MultiplicityOneConstituentProof`.

`Langlands.Classification.positiveTotalHeadCriterion` proves exactly
`PositiveTotalHeadCriterionStatement` with independent group, monoid,
source-carrier, image-carrier and test-carrier universes.

The imported `Langlands.Classification.smoothProduct` puts the actual product
action on the pair of carriers. For each pair of vectors it intersects the two
open subgroups fixing their coordinates. The imported
`Langlands.Classification.mappedProductSplitting` maps the four product
inclusions and projections through the additive functor.
Their identity and zero composites survive, so the paired image
projections admit a right inverse given by the sum of the image
inclusions. In particular those projections give an actual surjective
intertwiner onto the product of the two functor images. The helper also
retains injectivity of that right inverse, although the head argument uses
only surjectivity.

`positiveTotalHeadCore` chooses the supplied actual smooth irreducible
quotient and its count, at least the supplied positive total `m`. Given
any other algebraic irreducible quotient, surjective smoothness transfer
makes its target a smooth object, so the quotient-count premise applies.
If the two kernels differ, the published
`unequalIrreducibleQuotientKernels` theorem makes their paired quotient map
onto the smooth product surjective. Epimorphism preservation makes its
functor image surjective, and composition with the split paired image
projections produces a surjection from `F(A)` onto the product of the two
quotient images.

The supplied actual series witnesses give product multiplicity equal to
the sum of the two quotient-image counts, by
`jordanHolderProductAdditivity`. The surjection bounds that sum by `m`
using `jordanHolderSurjectiveMonotonicity`. Both counts are at least `m`,
so arithmetic contradicts `0 < m`. Consequently every irreducible
quotient kernel equals the chosen kernel, which supplies the existing
strong `HasIrreducibleHead` relation. The final theorem introduces the
closed statement's arguments and applies this core.

This is an internal algebraic derivation. All finite-series witnesses and
actual maps remain in the hypotheses. The proof uses no inequivalence of
the quotient targets and applies when they are isomorphic or identical.
It adds no irreducibility of the test representation, finite dimension,
admissibility, topological-group instance or monomorphism preservation.
It does not supply the quotient existence or count hypotheses for a
particular Jacquet functor or induced representation.
