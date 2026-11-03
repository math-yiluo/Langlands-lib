# The affine-line correction to Conrad's Remark 3.3

This is a derived correction target for Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Remark 3.3, printed page 5.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The file defines propositions; their proof is a separate obligation.

## The wording defect

The remark distinguishes points in a closed subscheme Z and its open
complement U, but then describes the closed condition using nilpotence.
For the affine-line origin, actual factorization through the zero closed
subscheme requires the coordinate to be zero. Nilpotence instead means
that the underlying topological image of Spec S lies in the origin. Those
conditions differ for a ring with a nonzero nilpotent.

Consequently the local Artinian sentence needs a distinction. A local
Artinian spectrum has one point, so its underlying image cannot meet both
a closed subset and its complement. Actual scheme maps need not factor
through either member of that closed/open pair. This target supplies the
explicit epsilon point over the local Artinian ring of dual numbers; its
image lies in the origin and it factors through neither member. This
refutes any reading of the sentence that asserts coverage by Z(S) and U(S).
The field coverage statement is retained.

## Actual affine-line statements

For commutative R, an R-algebra S, and actual relative scheme points of
Spec(R[t]), `AffineLineStratificationProperties` has six clauses:

1. The actual open D(t) is the complement of the underlying image of the
   actual zero-section scheme morphism.
2. The whole underlying image of an S-valued point lies in that zero-section
   image exactly when its coordinate is nilpotent.
3. The image on S-points of the zero closed subscheme is precisely the
   zero-coordinate locus.
4. The image on S-points of the actual D(t) open subscheme is precisely the
   unit-coordinate locus.
5. The two point images are disjoint when S is nontrivial.
6. Their union is the whole point set exactly when every element of S is
   zero or a unit.

The coordinate equivalence and both strata are actual scheme constructions
from `AffineLineOrigin` and `AffineLinePuncture`. No point topology, locality,
open-unit, separation or faithfulness hypothesis is imposed. R and S lie
in a common arbitrary universe. The nontriviality premise is used only
for disjointness: in the zero ring, zero is a unit and Spec S is empty.
The other five clauses allow the zero ring.

## The combined correction target

`ConradRemark33Correction` asserts those six clauses for every such R and S.
It also asserts coverage for every field-valued point over any commutative
base ring acting on that field.

Finally, for every field K it takes the specific actual relative point
with coordinate epsilon over the base ring K[epsilon] itself. The point
is the inverse of `affineLinePointEquiv K[epsilon] K[epsilon]` at epsilon,
so this is the same-base setting of the printed affine-line example.
The target requires that K[epsilon] be local and Artinian, that epsilon be
nilpotent, that the point's underlying image lie in the origin, and that
the point belong to neither actual stratum's point image.

The source's field assertion is a special case of the algebraic
zero-or-unit criterion. The nilpotent-image distinction, separate-base
generalization and explicit dual-number counterexample are the stated
mathematical correction, rather than assertions attributed to the
printed remark. No general closed/open coverage result for arbitrary
schemes or remaining whole-paper assertion is claimed here.
