# Preservation and reflection of geometric Borel subgroups

Author: Worker 693.

This internal helper derives field-extension transport from published Library
results. It supports residue-fibre reasoning for arbitrary-base relative Borel
subgroups and introduces no new source-dependent definition.

`geometricPointPullbackProjection` is the projection from the pullback of the
chosen geometric-point test scheme along a morphism of field spectra, regarded
as a morphism over the original field. This is the actual projection used in the
solvability reflection argument.

`IsSolvableGroupScheme.of_baseChange` reflects geometric solvability along a flat
surjective morphism of field spectra when the pulled-back group is smooth and
affine. The published uniform solvability theorem makes its points on every
relative test scheme solvable. Pull back the original geometric-point test,
identify its points with the upstairs points, and inject the original point group
by restriction along the epimorphic projection.

`IsBorelSubgroup.of_baseChange` reflects the Borel property of a supplied closed
inclusion under every field extension, assuming the original ambient group is
affine. Smoothness and connectedness descend; solvability follows from the
previous helper. Every competing smooth connected solvable closed overgroup
remains such an overgroup after extension by the published connectedness and
solvability results. Maximality upstairs then makes the comparison invertible,
and fpqc reflection of isomorphisms descends this conclusion.

`IsGeometricBorelSubgroup.of_baseChange` reflects the geometric Borel property
under every field extension for the same supplied closed inclusion and affine
ambient group. The natural comparison between the two chosen algebraic closures
transports the upstairs Borel to the pullback of the original geometric fibre.
The preceding reflection lemma and geometric Borel descent finish the proof.

`IsGeometricBorelSubgroup.baseChange_of_smooth_affine` preserves geometric Borels in any smooth
connected affine ambient group under every field extension. The published
algebraically closed field-extension theorem preserves the original geometric
Borel. Naturality of the comparison of chosen closures identifies this with the
new geometric fibre; geometric Borel descent supplies the new field-level Borel.

These are internal deductions from the existing predicates, the published
solvable and algebraically closed Borel extension proofs, geometric connectedness,
and effective fpqc descent. They do not construct a Borel subgroup or an inner
form.

## Connected reductive compatibility interface

# Geometric Borel subgroups under field extension

This is a derived transport result for the existing geometric Borel predicate.
Its ambient group is connected reductive over a field, and the extension is an
arbitrary morphism between spectra of fields in the same universe.

`IsGeometricBorelSubgroup.baseChange` extends the algebraic-closure Borel by the
published `borelAlgClosedFieldExtensionStatement`. The natural comparison between
the two successive pullbacks identifies this inclusion with the
algebraic-closure pullback of the requested inclusion. The published Borel
descent theorem then supplies the Borel property over the extended ground field.
Closedness follows by base change of the original closed inclusion.

The argument uses existing Library theorems and pullback coherence; it introduces
no additional structural result about reductive groups.
