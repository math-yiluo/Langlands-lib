# Strong quasi-isomorphisms and actual selected-subatlas inclusions

This module constructs strong inclusions from locally refining selections of
original charts and proves their quasi-isomorphism property. It retains the
actual positive-polyradius presented algebras and all admissible bounded
pullbacks. It also defines strong quasi-isomorphisms, constructs their local
domain objects, and identifies each local spectrum homeomorphically with the
image locus.

The coefficient field `K : Type u` is a complete ultrametric normed field.
The space and chart-index universes `v` and `w` are independent of `u`. All
presentations in a strong map use the same triple `u, v, w`. The imported chart
algebras are genuine finite positive-polyradius Tate quotients by closed ideals;
no strictness or reducedness assumption is added.

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), Definition 1.2.3 and Remark 1.2.4(i), printed p.16, and Definitions
1.2.7 and 1.2.9, printed pp.18–19 (PDF pp.13, 15–16), registered as
`berkovich-1993-etale-cohomology`. The retained original is
`Berkovich--Etale cohomology for non-Archimedean analytic spaces--1993.pdf`,
SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These passages were reread for this construction. The prior bounded project
lookup found no source-specific errata note. Definition 1.2.9 requires an
ambient homeomorphism and affinoid-domain identifications for every admissible
pair of charts. The following selected-original-chart construction is derived
from these conventions and the published local-refinement construction; it is
not the general extension or calculus-of-fractions theorem.

For an actual indexed atlas `a`, `restriction_represents i j h` proves that the
original bounded restriction from the algebra of chart `j` to that of chart
`i` represents the locus
`a.chart j ⁻¹' Set.range (a.chart i)`. Here `h` is containment of the two chart
images. The imported exact spectrum-range theorem and compactness give the
closed-locus condition, and the atlas's original `restriction_universal`
supplies unique bounded factorization against every
`PresentedAffinoidAlgebra K` test. In particular, the tests include nonstrict
finite positive-polyradius presentations. `restrictionDomain` bundles precisely
this algebra, bounded structural map, relative locus, and proof into an actual
`PresentedAffinoidAlgebra.Domain`. It assumes no new domain algebra.

For `f : StrongHom A B`, `chartImageLocus i j` is the preimage, under the target
chart `j`, of the ambient image of the source chart `i`. At an admissible pair,
`range_pullback` proves that this is exactly the image of the actual spectrum
comap of `f.pullback i j h`. The forward direction uses the chart square.
For the reverse direction, a source-chart point witnessing membership supplies
the preimage point, and injectivity of the target chart proves its spectrum
equality. This argument requires neither injectivity nor a homeomorphism of the
ambient map. `isCompact_chartImageLocus` then uses the continuous image of the
compact actual source spectrum; the target spectrum is Hausdorff, giving
`isClosed_chartImageLocus`. These assertions require the supplied admissibility
proof `h`.

`StrongHom.IsQuasiIso` is a `Prop`-valued definition. Its first conjunct is
`IsHomeomorph f.baseMap`. Its second requires the actual bounded pullback at
every admissible pair to satisfy the full imported `Represents K` predicate
for `chartImageLocus`. Thus it includes closedness, exact spectrum image, and
unique bounded factorization against all the presented affinoid tests above.
It does not replace the bounded algebra information by a condition on points.

For a proof `hf : f.IsQuasiIso`, `hf.localDomain i j h` uses the existing
source algebra, the actual pullback, and the second conjunct of `hf`.
`hf.isEmbedding_pullback` separately proves that the local spectrum map is an
embedding: after composing it with the target chart, the chart square
identifies it with the composition of the ambient homeomorphism and the source
chart embedding. The target-chart embedding permits cancelling that composition.
This proof does not infer spectrum injectivity from `Represents` alone.
`hf.localHomeomorph` combines the resulting embedding-to-range homeomorphism
with `range_pullback` to identify the source spectrum with the actual image
locus. `localHomeomorph_apply_coe` records that its forward map is exactly the
spectrum comap of the original bounded pullback.

`isQuasiIso_id` proves the identity is a quasi-isomorphism. The ambient map is
the identity homeomorphism; every local bounded pullback of `StrongHom.id` is
the original atlas restriction, so its full representation property is
`restriction_represents`.

Given `P : A.atlas.Index → Prop` and
`hP : A.atlas.IsLocallyRefiningSelection P`,
`f.restrictSubatlasSource P hP` is a full strong map
`A.subpresentation P hP → B`. The published local-refinement construction has
already proved that this selected family is a net on exactly `A.space`.
The new strong map retains `f.baseMap`; for each selected source index `i`,
its target witness, every admissible pullback, chart square, and two-variable
restriction square are the corresponding original fields at `i.val`.
`restrictSubatlasSource_baseMap` and `restrictSubatlasSource_pullback` give the
exact data formulas. `IsQuasiIso.restrictSubatlasSource` proves that a
quasi-isomorphism remains one after this source selection: the ambient map is
unchanged and every selected pair is an original pair.

`A.strongSubatlasInclusion P hP` is the source restriction of the full strong
identity on `A`. Its ambient map is exactly the continuous identity, recorded
by `strongSubatlasInclusion_baseMap`. At every admissible selected/original
pair, `strongSubatlasInclusion_pullback` identifies its pullback with the
original bounded restriction. At the selected chart itself,
`strongSubatlasInclusion_pullback_selected` uses the original restriction
identity law to recover the bounded identity used by the published chosen
arrow `A.subatlasInclusion P hP`. Finally,
`isQuasiIso_strongSubatlasInclusion` follows by source restriction of
`isQuasiIso_id`. This constructs all admissible local maps and their domain
factorizations without imposing upper cofinality or directedness.

The local-refinement witness is essential: arbitrary chart deletion is not
claimed to preserve an atlas. This module neither supplies an inverse strong
map nor asserts an isomorphism in a category of supplied atlases. General
extended atlases, finite affinoid gluing, unrestricted strong composition,
closure of arbitrary quasi-isomorphisms under composition, and the calculus
of right fractions of Proposition 1.2.10 remain separate obligations.
Structure sheaves, étale and equivariant sites, and the Harris tower are also
outside this focused construction. Only the published strong-map,
selected-subatlas, and full affinoid-domain foundations are used.
