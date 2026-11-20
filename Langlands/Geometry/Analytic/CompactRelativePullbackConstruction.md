# Compact continuous relative pullbacks over the ambient analytic space

`compactContinuousRelativePullback` takes a cospan of compact Hausdorff
objects `U ⟶ B ← V` in `QuasiEtaleSite X`. It constructs a limiting
site cone and a continuous action on its compact Hausdorff vertex. The
given actions on `U` and `V` are continuous, the two arrows intertwine
them with the action on `B`, and the structure map `B ⟶ X` intertwines
that action with the one on `X`.

`localizedQuasiEtalePullback` constructs the full products of `U` and
`V` and of `B` with itself over `X`. The map between the products sends
the two projections to their composites with the arrows into `B`.
`compactQuasiEtaleDiagonalDomain` realizes the diagonal of `B` as an
analytic domain of its self-product. `compactRelativePullbackOfDiagonal`
pulls back that domain along the map between products. It supplies
compact Hausdorffness and the full localized pullback property over `B`.
The ambient space `X` is arbitrary.

The two structure maps of `U` and `V` admit local factorizations through
analytic domains in étale envelopes. `of_isPullback_common` gives these
factorizations for the product over `X`, and `domainι_comp` restricts
them to the cut. This proves that the cut's structure map is quasi-étale.
`quasiEtalePullbackIsLimit` then uses the localized universal property
to obtain the unique site map from every test cone over the cospan.

The two pullback actions are determined by their projections.
Projection uniqueness makes the inclusion of the cut equivariant.
The quasi-étale first leg supplies the smallness of the product over `X`,
to which `isContinuousAction_of_isPullback_of_quasiEtale` applies.
`IsContinuousAction.of_equivariant_domainEmbedding` gives continuity
on the cut. The data retain the equivariance of both projections.

This is an internal construction for the tuple-cone proof. Worker 659
proved compactness of the cut and continuity for the product and its
domain. Worker 611 proved the diagonal and common-product results and
assembled the relative pullback.
