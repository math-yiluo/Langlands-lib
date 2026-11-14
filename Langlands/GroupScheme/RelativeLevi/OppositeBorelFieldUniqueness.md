# Uniqueness of an opposite Borel through a maximal torus over a field

Worker 608.

This is a private auxiliary proof draft for the relative opposite Borel
task. It has not been accepted or published.

`oppositeBorel_range_eq_of_isSplitTorus` works over every field and assumes
that the fixed maximal torus is split. For two Borel subgroups whose
intersections with a fixed Borel subgroup equal that torus on all test
schemes, it proves equality of their image subgroup functors.

The proof uses the third clause of the published
`regularCocharacterBorel` theorem to write each Borel as the dynamic
parabolic of a regular cocharacter of the fixed torus. Containment of
the torus, obtained from the intersection equality, supplies the
factorizations required by that theorem. The published
`centralizer_comp_eq_range_of_isRegular` identifies all three dynamic
centralizers with the fixed torus. Evaluation of the intersection
equality on the identity test scheme then permits the use of the
published `oppositeDynamicParabolicUniqueness` theorem. Both candidate
Borels consequently equal the dynamic parabolic of the negative of
the cocharacter chosen for the fixed Borel.

This is an internal application of those Library results. It is the
split-torus field uniqueness part of Conrad, *Reductive group schemes*
(2014), Proposition 1.4.4 (pp.32–34), used on geometric fibres in the proof
of Proposition 5.2.12 (p.158). The proof does not assume that the field
is algebraically closed.

`oppositeGeometricBorel_range_eq` extends uniqueness to possibly nonsplit
maximal tori when all three Borel subgroups satisfy
`IsGeometricBorelSubgroup`. It passes to the algebraic closure, where the
published maximal-torus base-change and finite-Galois-splitting theorems
make the given torus split. The second clause of the geometric Borel
predicate supplies Borelness of the base-changed subgroups. Images and
intersections commute with base change, so the first theorem applies.
Fpqc reflection of equality of represented subgroup functors then gives
the desired equality over the original field.
