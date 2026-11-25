# The image functor of a compact isotypic projector

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, (IV.1.5.1) and IV.1.5 Remark 3,
printed pp. 93–94 (PDF pp. 99–100). Registered source
`renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

In `Langlands.Renard.CompactRepresentation.ProjectionDistribution`,
`projectorImageFunctor μ D` sends each smooth representation `A` to the
actual invariant image of the published compact isotypic projector for `D`.
A morphism maps the image to the image by naturality. The displayed
functor (IV.1.5.1) uses precisely this operation on objects and morphisms.
The identification with `π(e_τ)` follows from the published `action_element`
formula on a vector fixed by a compact open subgroup.

`projectorCenter μ D` gives that same family of projectors as a member of
`CategoryTheory.CatCenter`, the natural endomorphisms of the identity functor.
The inclusion of the image and the projector corestricted to the image
are natural. Projecting after inclusion gives the identity on the image
by idempotence, while including after projection gives the original
central endomorphism. These intrinsic laws describe the actual splitting
used to formulate the separate exactness assertion.
