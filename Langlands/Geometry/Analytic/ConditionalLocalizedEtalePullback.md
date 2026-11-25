# Exact localized etale pullbacks from two general analytic criteria

This internal conditional construction obtains the exact existing
`LocalizedEtalePullbackStatement.{u,v} K` from two explicit assumptions:
`FiniteOverTargetLocalityStatement.{u,v,v} K` and
`FinitePiecesEtaleAllPiecesStatement.{u,v,v} K`. The field universe and
space/index universe remain independent. The field is an arbitrary
complete ultrametric normed field. No Hausdorff, compactness, equal-universe,
nonempty-space, supplied pullback or additional lifting premise is retained.
The two stated general analytic assumptions are not proved here.

For an actual saturated strong cospan with a strong etale first leg, the
existing recognition-source and recognition-base comparisons replace it
by the canonical selected recognized cospan. The proved finite Banach
quotient-smallness criterion constructs the canonical small quotient in
the original space/index universe. The actual small compatible second
projection has the all-pieces etale certificate supplied by the preceding
conditional neighborhood assembly. The canonical strong etale comparison
identifies this with the existing strong predicate on the constructed
saturations. Composing with the target's actual saturation quasi-isomorphism
makes the existing geometric small second projection strong etale.

The existing `recognizedLocalizedPullback` supplies an actual limiting
cone over the original mapped strong cospan, with the full universal
property on complete localized morphisms. Its second projection is the
map of that same geometric small second projection followed by the inverse
of the actual recognition-source comparison isomorphism. Existing localized
etale composition and isomorphism invariance make this entire second leg
etale. No new point-map representative replaces its bounded coefficients.

The proved strong/localized pullback reduction converts this entire
localized limiting square and etale second leg to refined strong data.
Its existing arbitrary-fraction construction then gives the exact original
localized statement for every localized cospan with an etale first leg.
The universal property is Mathlib's complete `IsPullback`, and the second
leg satisfies the pre-existing localized `etale` predicate.

An initial theorem states finite Banach pushout and full finite tensor
comparison as additional explicit inputs. The final theorem
`localizedEtalePullback_of_targetLocality_and_finitePieces` discharges both
with the published unrestricted proofs `AffinoidPushout.finiteBanachPushout`
and `AffinoidPushout.finiteTensorComparison`. Their paired source has no
nontrivial-valuation or strict-radius premise. Thus exactly the two general
analytic criteria remain as assumptions. The data construction
`conditionalLocalizedEtalePullback` chooses an actual pullback cone with
its `IsLimit` data and a lifted proof that its second leg is etale.

The provenance is internal: original-domain localized universality,
complete canonical small projection coefficient and finite-neighborhood
assembly, actual recognition/saturation comparison isomorphisms and the
existing strong/localized fraction reduction. The two finite algebra
comparison proofs are reused unchanged from the Library. This is a
conditional definition and theorem, not an unconditional proof of
`LocalizedEtalePullbackStatement`. The two general analytic criteria are
proved in the Library by `finiteOverTargetLocality`
(`FullRecognitionFiniteTargetLocalityProof`) and `finitePiecesEtaleAllPieces`
(`FinitePiecesEtaleAllPiecesProof`); `SpaceAnalytificationEtaleFromSourceDescent`
applies this theorem to them for equal field and space universes.
