# Smooth closed overgroups from standard rational-point classification

Worker 1358. This is an internal derived adapter between the published rational
standard-parabolic interfaces and smooth closed subgroup functors.

Over an algebraically closed field `k`, let `G` be smooth affine, let
`j : T.toGrp ⟶ G` be a specified torus map, let `ν` be an integral cocharacter
of `T`, and let `i : P ⟶ G` be a smooth closed subgroup. Suppose the actual
dynamic subgroup `P(ν ≫ j)` is contained in the range of `i` on every test
scheme. Two local structural inputs suffice:

- Every abstract subgroup of `G(k)` containing `P(ν ≫ j)(k)` is the subgroup
  of field points of `standardParabolic j ν J` for some subset `J` of the
  simple relative roots.
- For each such `J` there is an actual integral standard cocharacter `ζ` of
  the same `T`, and the standard subgroup functor is `P(ζ ≫ j)` on every
  test scheme.

The theorem `nonempty_standardDynamicOvergroupData_of_points` constructs a
standard index `J` and an actual `ζ`, with its standard-cocharacter predicate
and equality
`SubgroupFunctor.range i = Dynamic.parabolic (groupHom ζ ≫ j)`.
The structure `StandardDynamicOvergroupData` retains these data and proofs.
The local theorem needs no connectedness, reductivity, maximality of the
torus, or genericity beyond what the two displayed local premises supply.

The definition `standardDynamicOvergroupData_of_statements` obtains those
local premises from the explicitly assumed
`StandardParabolicPointsStatement` and `StandardCocharacterStatement`.
This specialization additionally assumes connected reductivity, a specified
maximal split torus, and a generic `ν`. It uses only the overgroup clause of
the first statement and the parabolic clause of the second.

## Implemented proof and scope

Apply the field-point overgroup classification to the image of `P(k)`.
Choose the supplied standard cocharacter for the resulting index. Evaluation
of the all-test standard-parabolic equality identifies this image with the
field points of the dynamic parabolic. The published theorem
`Dynamic.range_eq_parabolic_iff_algClosed_points` then gives equality of
the subgroup functors on all test schemes: both closed subgroup schemes
being compared are smooth.

The two structural classification inputs remain premises. This module does
not prove either global statement, produce a generic dynamic subgroup inside
an arbitrary parabolic, or prove the fixed-torus classification without
additional assumptions. It does not change the field, specified torus or
torus map, replace integral cocharacters by rational ones, or restrict the
equality to field points. The argument applies also when the relative-root
set is empty, provided its displayed premises hold.
