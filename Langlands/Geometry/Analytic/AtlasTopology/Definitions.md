# Topological families for affinoid atlases

Author: Worker 36.
Documentation correction (I005): Worker 333.

The original is Vladimir G. Berkovich, *Etale cohomology for
non-Archimedean analytic spaces*, Publications mathematiques de l'IHES 78
(1993), section 1.1, printed pages 13–14 (PDF pages 10–11). The retained
source is `C:/Central-Library/Berkovich--Etale cohomology for non-Archimedean analytic spaces--1993.pdf`,
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

`IsQuasinet` requires at each point a finite family of members which all
contain that point and whose union is a neighborhood. Finite subsets of
the collection replace the finite lists in the source; repetition in a
list changes neither its intersection nor its union. Nonemptiness of
this family follows from the neighborhood condition.

`restrictedFamily` uses only members contained in the specified
subspace. Its members are their actual inverse images under the subtype
inclusion, with the induced topology. `IsNet τ` requires both that
`IsQuasinet τ` holds for the original family on the whole space and that
`IsQuasinet (restrictedFamily τ (U ∩ V))` holds for every `U, V ∈ τ`.
No intersection-closure assumption is added.

The source assumes that compact spaces are Hausdorff. Accordingly
`IsCompactFamily` requires both `IsCompact V` in the ambient space and
`T2Space V` for each member. The ambient space itself need not be
Hausdorff. `productFamily` is the actual family of rectangles used in
Lemma 1.1.1(ii).

These are topology prerequisites for the atlas in Definition 1.2.3,
printed page 16. They do not define an analytic space, supply affinoid
domain structures, or assume acyclicity, cohomology or comparison results.
