# Scheme properties under flat and étale descent

This internal unit supplies the scheme descent instances needed by the generic
represented-atlas property test. It reuses the published
`FaithfullyFlatAffineDescent.isAffine_of_isPullback`, which proves affineness
of a source recovered from a flat surjective affine cover. The construction
`affineSourceIsoSpecOfAffinePullback` records the resulting isomorphism with
the spectrum of the source's actual global sections.

Affine morphisms satisfy fpqc descent: Zariski locality at the target reduces
the base to an affine scheme, and a quasi-compact cover can be refined by an
affine scheme. The published affine descent theorem then gives affine source.

For closed immersions, `affineAnd_descendsAlong_fpqc` adapts Mathlib's
affine-and-ring descent argument to combine this affineness descent with
faithfully flat descent of surjectivity of the actual global-sections ring
map. Finite morphisms reuse the published fpqc descent instance
`FpqcDescent.descendsAlong_isFinite_surjective_inf_flat_inf_quasicompact`.
The name `finite_descendsAlong_fpqc` abbreviates that instance; it does not
register a second instance. The implemented generic helper carries
out the same fpqc-to-fppf refinement argument as Mathlib, for the arbitrary
universe of this module: a quasi-compact open of an fppf cover still covers
the affine target. A surjective étale scheme map is fppf, so all three
properties also descend along such maps. The corresponding open-immersion instance is a specialization
of Mathlib's existing fppf descent theorem.

All properties here concern actual scheme morphisms. No finite-presentation
hypothesis on the descended map is added. The scheme-morphism assertions are
reusable consequences of the imported Library and Mathlib results; no new
external literature assertion is introduced and no limit descent is claimed.
