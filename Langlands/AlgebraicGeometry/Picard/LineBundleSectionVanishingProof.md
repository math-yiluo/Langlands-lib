# Field-point vanishing and frame cancellation for line-bundle sections

This derived internal proof establishes
`Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingStatement`
in arbitrary universe `u`. It uses actual schemes, line bundles, sections,
pullback functors and the canonical tensor comparison. It requires no
algebraic closure, finite type, smoothness, properness, projectivity or
ampleness. It includes the zero tangent vector.

The field, trivialization-open and dual-number arguments are adapted from
Worker 899's shared `SectionCalculus` and `TensorFamily` drafts on task
`eda1f6ff-d036-4f23-aabb-7663e7606b42`, revision 2. Worker 354 extracted
them into the general Picard namespace, replaced their repeated transport
and tensor algebra with the generic section-transport and tensor-zero
proof APIs, and assembled the seven-clause theorem. Worker 152 retained
the seven public Picard lemmas and initially adapted the tensor comparison and
frame arguments as private helpers. The integrated module now imports the
public `Modules.TensorSectionZeroProof` API in place of those identical helpers.
Workers 354 and 899 are actual coauthors. No external literature theorem is
asserted here.

## Field-valued points

The zero section has empty trivialization open, using the published
comparison between that open and the residue nonvanishing locus. The
pullback-open comparison then implies that a section vanishing along a
morphism has no image point in its trivialization open.

For the converse over a field, `vanishesAlong_field_iff` factors the
field-valued point through its image's residue field, using Mathlib's
`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`.
Outside the trivialization open the residue section is zero. Its
pullback is therefore zero, and the composition transport theorem
identifies this with vanishing along the original point.

The field-point tensor rule follows from this equivalence and the
published equality between the trivialization open of a tensor section
and the intersection of the factors' trivialization opens.

## Cancellation along a morphism

A section whose trivialization open is the whole scheme has an
invertible section morphism, by the published stalk criterion. The
pullback-open comparison shows that a section generating at every image
point pulls back to such a section.

The imported `TensorSectionZeroProof` lemmas test a tensor section on its section morphism. Factoring
the tensor map through the framed factor makes one map invertible;
naturality of the explicit right or left unitor reduces the remaining
zero condition to zero of the other section morphism. Naturality and
invertibility of the canonical pullback tensor comparison identify the
zero test for the actual pulled-back tensor section with the tensor of
the two pulled-back sections. The tensor of the inverse unit comparison
is invertible and can be cancelled. The right and left cancellation
lemmas apply these helpers to the actual pulled-back frames. Thus they
preserve and reflect vanishing along the morphism. They do not cancel an arbitrary nonzero
section over a ring.

The auxiliary lemmas also identify the whole trivialization open with
invertibility of the section morphism, prove that the unit section of
the trivial line bundle generates everywhere, and express the
field-point test for a preimage open. These are used by the finite
product and translation assembly.

## Tangent vectors

Every element of the dual numbers over a field is a unit or nilpotent
(`TrivSqZeroExt.isUnit_or_isNilpotent`). An element of a prime ideal
cannot be a unit, and every nilpotent belongs to every prime ideal.
Consequently any two prime ideals coincide.

The one point of the dual-number spectrum is the augmentation image of
the field's closed point. The defining restriction equation in
`IsTangentVectorAt` identifies its image under the tangent with the base
point's image. By the field-point test, nonvanishing at the base point
therefore puts every tangent image point in the section's
trivialization open. The morphism cancellation lemmas now give both
tangent cancellation statements.

The final theorem `lineBundleSectionVanishing` packages these results in
exactly the order of the unchanged statement. It imports the published
section-transport and generic tensor-zero proofs, together with the tensor and
unitor constructions. The generic `TensorSectionZeroStatement` target is proved
in the imported `Modules.TensorSectionZeroProof` module; this module specializes
its cancellation lemmas to line bundles.
