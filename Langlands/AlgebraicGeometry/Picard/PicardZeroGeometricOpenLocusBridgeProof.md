# The all-test Picard-zero criterion from a geometric-point locus

Worker 390 authored this proof, extracted into shared draft revision 3 from
the revision-2 `FieldPicardZeroOpenLocusAssembly`. Worker 1735 reused the
extracted Lean proof unchanged and prepared this proof submission. It retains the public helper name
`Langlands.AbelianScheme.isPicardZeroOpenLocus_of_geometricPoints` and
packages it as the exact proposition
`PicardZeroGeometricOpenLocusBridgeStatement.{u}` through the theorem
`Langlands.AbelianScheme.picardZeroGeometricOpenLocusBridge`.
The proof imports the published statement module
`Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricOpenLocusBridgeStatement`
and preserves its definitions and imported closure.

The proof takes geometric detection and the exact geometric-point
criterion for a supplied open U as inputs. It constructs no open set.
All bases, actual families, fields and test schemes retain universe u;
the test schemes may be nonreduced or non-quasi-separated, with no added
finiteness or universality hypotheses.

First, `exists_geometricPoint_over` takes the algebraic closure of the
residue field of a point x of a scheme X. The composite spectrum map to
X sends its chosen point to x by `Scheme.fromSpecResidueField_apply`.
Consequently `range_subset_iff_geometricPoints` detects containment of
any scheme morphism's range in any subset after all geometric-point
maps into its source.

Next, `picardZeroFamily_relativePullback_comp` applies the existing
`RigidifiedLineBundle.classifyingMap_comp` with
`RigidifiedModule.pullbackCoherence`. Applying `IsPicardZeroClass A` to
that equality identifies the predicates on iterated and direct actual
relative pullbacks. `picardZeroFamily_overHomMk_iff` substitutes an
equal structure map, aligning the slice object with the composite
map required by the geometric-point criterion.

For every test T and actual h from T to P,
`isPicardZeroClass_classifyingMap_iff` identifies classifier membership
with the predicate on the actual family pulled back along h.
Geometric detection reduces that predicate to further pullbacks along
all geometric points of T. The pullback comparisons identify each
with the direct composite into P. The supplied geometric-point
criterion and detection of range containment then give exactly
`IsPicardZeroOpenLocus A L U`.

This is internal derived content, not a claim that any original source
states this exact interface. It neither establishes geometric openness
nor completes the field or relative open-existence theorem. The supplied
open and geometric detection remain explicit premises.
