# Actual base-change framing squares on arbitrary further refinements

This internal unit constructs the actual full-order target isomorphism and
proved framing square between any specified new and original further-refined
charts on a new quotient test ring. The original test is restricted along the
actual reduced Nilp scalar map. Each supplied chart has its actual unit evidence;
no compatibility of choices of source generators is required. This extends the
previous canonical unrefined framing square rather than assuming a further
framing certificate.

`originalRefinedTargetTestIso` follows the actual reduced-target chart transition
from the specified original parent chart to the parent selected by the original
further refinement, then the inverse actual refinement chart identification.
The existing `chartFraming_transition` equation and the definition of the refined
chart framing prove `chartFraming_originalRefinedTargetTestIso` for the complete
rational maps.

`originalRefinedTargetOnRestrictedTestIso` transports that actual integral
isomorphism using the proved equality between the restricted and new test scalar
structures. `normalizedOriginalFraming_refinedTarget` transports its proved
framing equation, using preservation of composition and rationalization by the
global actual quasi-isogeny scalar transport. Both actual rational inverses are
retained throughout.

`baseChangeRefinedTargetTestIso` first uses the actual new refinement chart
identification, then the previously constructed canonical base-change target
chart comparison, then the transported original correction. Consequently it
also accounts for different old chart choices on the same restricted test.

`refinedChartFraming_baseChange` combines the canonical normalized framing
square with the proved identification of its original framing and the original
refinement equation. The generic `refinement_transport` reassociates the actual
composites and cancels the inverse new refinement correction. Rationalization
preserves the complete integral target composite.
`baseChangeRefinedFramingSquare` packages the four specified actual full-order
rational quasi-isogenies and the resulting equation. Its left side is the direct
fixed-frame test comparison, which has no chart parameter.

All constructions retain the local-field, central-division, embedded-field,
coefficient and residue hypotheses, height-certified fixed frame and Nilp
universes `{v,u}` of the original framed atlases. Covers may be infinite;
coefficient maps may merge cover generators. The generic cancellation lemma
allows arbitrary rings and rational fields with the existing domain and
fraction-field assumptions and a finite coordinate type. No representability,
extended original comparison preservation or comparison-class functoriality
is asserted here.
