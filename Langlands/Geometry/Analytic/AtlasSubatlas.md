# Same-space subatlases selected by relative local refinement

This module constructs a selected subatlas of a supplied genuine
`IndexedAffinoidAtlas`. It uses
`Langlands.Analytic.AtlasTopology.LocallyRefines` and its proved net criterion
from [AtlasTopology/Refinement.md](AtlasTopology/Refinement.md).

The original conventions are Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), §1.1, printed pp.13–14
(PDF pp.10–11), and Definition 1.2.3 and Remark 1.2.4(i), printed p.16
(PDF p.13), registered as `berkovich-1993-etale-cohomology`.
The retained original is
`Berkovich--Etale cohomology for non-Archimedean analytic spaces--1993.pdf`,
SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These passages were reread for this construction; no source-specific project
errata file was found. Selecting a locally refining family of original charts
is a derived construction using these definitions, not a separately numbered
source theorem.

For a predicate `P` on the original chart indices, `selectedChartFamily P`
is the family of ranges of precisely those original charts whose indices
satisfy `P`. `IsLocallyRefiningSelection P` is a proposition giving the finite
relative local refinement witnesses inside every original chart. In
particular, the input does not include an output atlas or a proof that the
selected family is a net.

`isNet_selectedChartFamily` proves the selected family is a net: it is a
subfamily of the original net, and the imported refinement result proves both
the ambient quasinet condition and the contained-member intersection
conditions. The proof applies to arbitrary overlapping chart ranges.

`subatlas P hP` has the same underlying topological space and chart indices
`{i // P i}`. It retains each original positive-polyradius presented affinoid
algebra, chart embedding, and bounded restriction map literally. Domain
injectivity follows from original domain injectivity and subtype extensionality.
The ambient local Hausdorff property is unchanged, the net property is proved
as above, and the full universal factorization against every presented
affinoid test algebra is inherited from the corresponding original pair of
charts. The bounded identity and composition laws are likewise the original
laws. The `subatlas_algebra`, `subatlas_chart`, `subatlas_restriction`, and
`subatlas_chartFamily` formulas record these exact data.

For a bundled presentation `A`, `subpresentation P hP` retains exactly
`A.space`. `subatlasInclusion P hP` is an arrow in the published category of
monotone chosen atlas maps. Its underlying continuous map is the identity,
its chart map forgets the selection proof, and its algebra pullbacks are
actual bounded identities. The chart and restriction squares hold by
reduction. `subatlasMap` gives the corresponding arrow between nested
locally refining selections. Its identity, composition, and factorization
through `subatlasInclusion` are equalities of full chosen arrows, proved
using `Hom.ext`, including the dependent bounded pullback field.
`spaceFunctor_subatlasInclusion` proves that forgetting the chosen data gives
the identity on the original space.

This constructs selected original-chart subatlases on an unchanged space. It
does not assert that arbitrary chart deletions preserve a net or that enough
original charts lie inside every open subspace. It supplies neither new
affinoid-domain algebras nor the extended atlas of Berkovich Proposition 1.2.6.
The chosen inclusion is not asserted to be an isomorphism in the chosen
category; no inverse chart selection, localization, structure sheaf, or site
is constructed in this module. The field, space, and chart-index universes
are independent `u`, `v`, and `w`.
