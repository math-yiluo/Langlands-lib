# The degree-one twist on relative projective space

This module defines the actual invertible module O(1) on relative projective
space over an arbitrary scheme by pulling back the degree-one twist of the
integral polynomial-Proj model. It also constructs its coordinate sections,
their whole generation opens and canonical comparisons under base change.

The convention follows the discussion after Definition 27.13.2 and before
Lemma 27.13.3 in Stacks Project Section 27.13, registered original
`stacks-projective-space-twists-morphisms-2026-10-26`, local file
`literature/Stacks Project - Projective space, twists and projective morphisms (HTML snapshot 2026-10-26)/01ND.html`.
The chart cover follows Lemma 27.13.3. The pullback construction and its
categorical comparisons here are internal consequences of these definitions
and of the existing integral coordinate-frame and generation-open proofs.

`integralTwistOne n` packages the actual integral twisting sheaf as a line
bundle using the published proof of local rank one. `twistOne S n` applies
the actual line-bundle pullback along the integral projection. Local rank one
is supplied by the published unconditional pullback construction.
`twistOnePullbackIso n f` composes the sheaf-pullback composition comparison
with the equality of the integral projections. `baseChangeTwistOneIso` then
uses the Cartesian scheme isomorphism and its second projection identity.

The coordinate sections are the actual `pullbackSection` images of the
integral homogeneous coordinates. `twistOnePullbackIso_coordinate` proves
that the canonical comparison carries the pullback of each coordinate to
the corresponding coordinate over the new base.
`baseChangeTwistOneIso_coordinate` gives the same equality after the two
successive pullbacks through the actual Cartesian product. These statements
concern the sections themselves, including their normalization.

The coordinate comparison reuses the published
`LinearSystem.pullbackSection_comp` from `LinearSystem/SectionRatio`.
This identifies iterated pullback of actual sections with pullback along
the composite, using the canonical composition isomorphism. The public
helper `pullbackSection_comp_eq` reduces an equality of scheme maps to reflexivity. It is also reused by the linear-system twist comparison.
Applying this helper to the integral projections
proves the first coordinate identity; applying it to the Cartesian
projections and then using the first identity proves the second.

The charts are the inverse images of
the integral coordinate charts. The integral cover pulls back to a cover.
The published theorem on whole generation opens of pulled-back line-bundle
sections, together with the integral coordinate generation-open theorem,
identifies each full generation open with its relative chart. Maximality
then proves that the coordinate section is a frame there. Inverse images
of coordinate charts commute with every base morphism by equality of the
integral projections.

The base scheme is unrestricted, and dimension zero and the empty base are
included. The module asserts no relative ampleness, universal mapping
property for generated line bundles, ring-base Proj comparison, nontrivial
projective bundle or embedding theorem.
