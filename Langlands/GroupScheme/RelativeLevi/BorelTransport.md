# Relative Borel subgroup transport

This module derives transport properties of the existing relative Borel and
relative parabolic predicates.

Source and ambient group isomorphisms preserve both predicates. For each residue
fibre this follows from the corresponding field-level transport theorem.
Smoothness and affineness of the source and the monomorphism condition are
preserved by the same isomorphisms.

For a reductive ambient group, `IsRelativeBorelSubgroup.fieldPoint` extends the
geometric Borel property from the residue field at the image of a field-valued
point to that point's actual coefficient field. It uses
`IsGeometricBorelSubgroup.baseChange`, the canonical factorization through the
residue field and the natural pullback-composition isomorphisms.

`IsRelativeBorelSubgroup.baseChange` applies this field-point result to each
residue-field point after an arbitrary scheme base change. Pullback stability of
smoothness, affineness and monomorphisms supplies the remaining relative
parabolic conditions. Reductivity of the ambient group is an explicit hypothesis
in these two results.

`relativeBorelBaseChange` packages this operation on actual relative Borel data:
it returns the pullback source, the pullback inclusion and its proved relative
Borel property.

All results are derived from the existing Library predicates, field-extension
theorems and pullback coherence. They do not assert the existence of a Borel
subgroup or of its parameter scheme.

The relative-parabolic source and ambient isomorphism lemmas are imported
from `ParabolicBaseChange`. Their hypotheses and conclusions are shared
unchanged by the relative-Borel transport results.
