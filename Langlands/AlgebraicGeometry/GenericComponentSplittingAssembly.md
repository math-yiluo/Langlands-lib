# Actual generic-fibre comparison for finite étale component splitting

This internal construction unit supplies the actual cartesian comparison
needed to assemble Stacks 0551 from the two separately stated existence
inputs `FiniteSeparableComponentSplitting` and `FiniteSeparableGenericCover`.
It does not prove either of those inputs.

`cartesianComparisonMapOfBaseIso` constructs a scheme morphism between
two cartesian squares over a common original morphism when an actual
isomorphism identifies their base maps. The universal property of the
second cartesian square defines the comparison. Pullback pasting and
cancellation show that the resulting square is the base change of the
specified isomorphism. The component geometry comparison then uses
`SchemeComponentGeometry` and its exact closed-support argument for
actual reduced vanishing-ideal component schemes.

`fiberComponentsGeometricallyIrreducible_iff_of_generic_specIso` applies
this construction to the actual residue-field fibre of a cartesian
cover diagram and a field scalar extension of the original fibre.
Both squares are obtained by pasting actual pullback squares. The
specified isomorphism between the extension field's spectrum and the
cover point's residue-field spectrum, together with its structural
triangle, identifies their base maps to the original scheme. No
assumption that base change preserves reduced schemes is used.

The final conditional assembly lemma chooses the original scheme's
generic point. Its actual residue-field fibre is Noetherian because
it is a locally finite-type, quasi-compact scheme over a field;
the original base is not assumed Noetherian. This gives the finite
component hypothesis for `FiniteSeparableComponentSplitting`. The
specified finite separable extension is passed to
`FiniteSeparableGenericCover`, and the preceding cartesian comparison
transfers its actual component geometry to the cover's generic fibre.
Surjectivity, finiteness and étaleness of the first projection are
Mathlib's actual base-change instances. The source of the projection
is the actual pullback of the actual open restriction, with target
the open-restricted source.

All schemes and fields use arbitrary common universe `u`. The resulting
theorem is explicitly conditional on both existence inputs. It is an
internal assembly result and is not a proof of the unconditional task
target until both inputs have been proved. Its mathematical provenance
is the categorical assembly in the registered Stacks 0551 proof, using
Mathlib's cartesian universal properties and published component transport.
