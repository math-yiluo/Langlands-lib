# Actual small etale projection from the two general analytic criteria

This internal conditional assembly proves all-pieces etaleness of the
existing complete canonical small second projection. The field and
space/index universes are independent. Smallness of the actual raw quotient
is explicit. The original first map is etale over all pieces.

Four inputs are stated explicitly: the general target-local finiteness
criterion, the general finite-pieces-to-all-pieces etale criterion, finite
Banach pushout base change and the full finite tensor comparison. This
module proves none of these four general inputs.

At any actual small quotient point, its first and second images have the
same base image. The original all-pieces etale first map supplies the
previously constructed genuine finite product neighborhood, including open
Hausdorff factor and common-base patches and its complete pointwise first
certificate. The existing actual small-projection neighborhood assembly
then gives `HasFinitePiecesAt` for pointwise etaleness. It uses the general
target-local criterion to assemble finite-over data, and the original
coefficient comparisons and finite tensor base change supply the property
on every tested recognized preimage of each chosen target piece.

An original local product index is needed only at a given quotient point.
It is obtained from the canonical small atlas's proved chart cover and
then unshrunk through the index equivalence. Thus no nonempty-space or
nonempty-index premise remains in the result. When the product is empty,
the pointwise assertion is vacuous.

Apply the supplied finite-pieces upgrade at every actual small point.
This gives joint all-pieces flatness and unramifiedness everywhere. The
whole small space is an open neighborhood, so these pointwise assertions
give the existing `IsEtaleAllPieces` predicate. The data construction
`etaleRecognitionSmallSnd` retains exactly the existing canonical small
saturation projection and its proved conditional all-pieces certificate.
It does not replace the bounded pullbacks by a new point-level morphism.

The provenance is internal: actual canonical small projections, chart
coverage, genuine finite product neighborhoods, complete full-recognition
projection coefficient identities, finite target families and the two
explicit general analytic criteria. This is a conditional theorem and
certified data construction. By itself it does not provide an unconditional
proof of the localized etale pullback statement `LocalizedEtalePullbackStatement`;
the two general criteria are proved in `FullRecognitionFiniteTargetLocalityProof`
and `FinitePiecesEtaleAllPiecesProof`.
