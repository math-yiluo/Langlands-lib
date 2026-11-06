# The fixed-level presheaf of full Tate-normalized CM models

Author: Worker 344.

This internal construction uses the existing universe-zero Harris CM data,
the `Prerequisites` package, and the named duality, polarization, finite Weil,
adelic comparison and torsion inputs of the original CM presheaf. It works on
the full category of connected admissible CM test bases at a fixed original
Harris level.

The value is `TateNormalizedCMGeometricFamily`: compatible families of the
actual normalized rational-isogeny quotient classes over every geometric
point. `tateNormalizedCMFamilyPullback` uses
`tateNormalizedCMClassBaseChange` at each pushed geometric point. This
quotient map comes from the actual pullback of the abelian scheme,
polarization, rational action, integral order action and original fully
normalized level orbit. It does not choose a replacement representative by
inverting a comparison.

Pointwise forgetting of this pullback is the original unpointed CM
pullback. The original pulled-back family's compatibility, together with
the canonical comparison square and injectivity of pointwise forgetting,
proves compatibility of the normalized family. Injectivity of family
forgetting transfers the original identity and composition laws. These
constructions give `tateNormalizedCMUnpointedPresheaf` and the literal
natural transformation `tateNormalizedCMUnpointedForget`.

Under the explicit `ProperFibreAmpleAffineOpenStatement` and
`CommensurableInvariantLatticeRealizationStatement`, and containment of
the fixed level in the source integral lattice stabilizer, the existing
family equivalence gives `tateNormalizedCMUnpointedIso`. Its forward
natural transformation is exactly literal forgetting. These hypotheses
are needed only for the isomorphism, not for the presheaf or its pullback.

No new source theorem is asserted. This file does not extend to
disconnected bases, assert normalization preservation by all transporter
arrows, or construct a representing scheme. Division-case representability
remains open.
