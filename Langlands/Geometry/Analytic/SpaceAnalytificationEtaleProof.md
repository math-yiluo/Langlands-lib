# Analytification of algebraic spaces detects étale morphisms

`spaceAnalytificationEtale` proves `SpaceAnalytificationEtaleStatement`
with its original universe parameter and hypotheses. It applies to a
compatible map between the supplied analytifications.

For preservation, an algebraically étale morphism carries every étale
affine test point of the source to an étale test point of the target.
Compatibility makes its composite with the analytic chart étale.
These charts cover the source. The proof uses strong representatives
of the compatible map and the chosen chart, transported to full
recognition by the localization isomorphisms. The affinoid-to-affine
comparison identifies the map from each affinoid piece of the chosen
chart with an affinoid ring-valued point of the source algebraic space.

At a lift of each covered point, take aligned open finite étale
neighborhoods for the chart map and its composite. The separated
algebraic diagonal gives the relation on each composite affinoid
piece. Its projections are finite étale. The finite étale quotient
is identified with the image domain by the finite covers of its
charts. This recognizes the image in the atlas. Finite faithfully
flat algebra descent on the resulting pieces gives the all-pieces
étale condition at the covered point. Joint surjectivity gives
étaleness everywhere, and the localization isomorphisms transfer
it to the original compatible map.

For reflection, compose the analytically étale map with each source
étale test chart. The analytic composite reflects étaleness of the
corresponding affine test point using the chart-local affine
comparison. The finite-type affine test criterion then yields
étaleness of the algebraic-space morphism.
