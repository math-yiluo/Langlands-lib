# Faithful full field points as tests of bounded pullbacks

This internal module works over a complete ultrametric normed field `K`
and a normed extension field `L`, with independent algebra, space, chart
index, and extension-field universes.

Suppose the source atlas satisfies `HasAllLocalDomains`, as required
by the actual full-field-point pushforward `FieldPoint.map`. An
injective evaluation of a full field point on a source chart detects
the bounded pullbacks of two strong morphisms from any target chart
admissible for both. Indeed, equality of the image full field points
identifies their target-chart evaluations. The actual field-point
mapping formula identifies these with source evaluation composed with
the two bounded pullbacks. Injectivity of that source evaluation then
identifies the bounded maps.

With the same source `HasAllLocalDomains` assumption, if both atlases
have charts covering their whole spaces, injectivity
of the source evaluation in its global chart therefore detects the
entire strong morphism. The proof uses the existing top-chart
comparison, which detects complete strong morphisms by their top
bounded pullbacks.

Under `DomainCompletedResidueSurjectivityStatement` and completeness
of `L`, the existing global-chart character equivalence extends any
bounded global-chart character to a full field point. Its evaluation
is exactly the given character, so injectivity of the character
implies injectivity of that evaluation.

For a presented affinoid algebra with a `Small` spectrum in an
independently specified space universe, the saturated small-spectrum
construction supplies `HasAllLocalDomains` automatically and retains
the original singleton chart as a global chart,
with exactly the original algebra. Transporting a character through
this algebra equality and extending it gives a full field point of
the small saturated spectrum. If the character is injective, equality
of the images of this field point identifies complete strong maps
from this spectrum to any saturated global-chart target.

Finally, `FaithfulCharacterQuotient.testSource` takes the presented
quotient by the kernel of any bounded character on an affinoid
algebra whose spectrum is small in universe `v`. The quotient
spectrum is small in the same universe, so its saturated spectrum
defines an actual test object in `SaturatedAtlasPresentation.{u,v,v}`.
Its descended character is injective; the full field point
`testPoint` therefore detects complete strong maps to global-chart
targets. The source algebra may have nilpotents or a nonzero
character kernel before quotienting. Construction of this test
point and its equality-detection theorem retain the explicit domain
completed-residue comparison premise and completeness of `L`.

The provenance is internal: the proofs combine the actual full
field-point mapping formula, the global-chart character equivalence,
the complete top-chart affinoid comparison, the small-spectrum
construction, and the faithful-character kernel quotient. This does
not assert equality detection for maps into arbitrary nonseparated
targets or full field-point preservation of localized pullbacks.
