# Sections and affine generation opens for field ampleness reflection

This internal construction packages the canonical actual scalar sections
isomorphism for an arbitrary morphism `b : Spec K ⟶ Spec k` of field spectra,
when a specified line bundle becomes ample after base change. The line bundle
whose sections are compared can be any line bundle on the original scheme.
The construction first uses the accompanying topological setup to derive
compactness and quasi-separatedness of that scheme, then applies the
canonical QCQS sections comparison to the ring map `Spec.preimage b`.
Full faithfulness of `Spec` identifies its image with the given morphism
`b`. Flatness of this ring map follows because its source is a field.

Two geometric lemmas prepare the final ampleness argument. A whole
generation open contained in an affine open is affine: the published
`affineGenerationLocusIntersection` identifies it with the affine
intersection. This applies to every actual tensor power of the specified
line bundle because these powers are locally free of rank one.

The last lemma lifts a point through the surjective field base-change
projection and uses the published ample section-open basis to produce an
upstairs section of a positive actual tensor power whose generation open
contains that lift and lies inside the preimage of a chosen downstairs
neighbourhood.

These are internal deductions from the imported Library constructions and
Mathlib's field flatness, spectrum full faithfulness and pullback APIs.
They do not yet extract any downstairs section and do not prove the exact
ampleness-reflection statement.
