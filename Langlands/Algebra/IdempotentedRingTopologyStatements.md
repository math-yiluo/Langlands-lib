# Laws of the actual right-coordinate topology

Worker 6 authored the statement family. Worker 345 checked the original source,
verified the published prerequisites and complete interfaces, expanded the
documentation, and prepared the focused submission.

Every declaration uses the actual original `A : Type uA` with
`NonUnitalRing A`, its original operations and the published actual
`Idempotent A` and `idempotentedRingUniformSpace A`. Every assertion is a
Prop-valued definition. The topology and uniformity are installed locally
from that construction, with no ambient topological parameter and no
global instance. The definitions assert laws, and do not prove them.

`IdempotentedRingUniformAddGroup A` asserts `IsUniformAddGroup A` for
the actual uniformity. In Mathlib this means uniform continuity of the
original subtraction map on the product uniform space. It entails the
usual continuous additive-group operations, while retaining the precise
uniformity rather than merely some compatible topology.

`IdempotentedRingRightCoordinatesSeparate A` says that two original
elements are equal exactly when their right products by every actual
idempotent agree. `IdempotentedRingHausdorff A` asserts `T2Space A` for
the topology of the actual coordinate uniformity. No separated quotient
replaces the original ring in either assertion.

`IdempotentedRingLeftMultiplicationUniform A` asserts uniform continuity
of `a ↦ b * a` for every fixed original `b : A`.
`IdempotentedRingRightMultiplicationUniform A` asserts uniform continuity
of `a ↦ a * b`. In both definitions the domain and codomain carry the
same actual uniformity.

`IdempotentedRingTopologicalRing A` asserts `IsTopologicalRing A` for
the original nonunital ring and the topology of the actual uniformity.
Mathlib's class allows nonunital rings and requires continuous original
addition, negation and jointly varying multiplication. Thus this target
includes joint continuity, beyond the two separate uniform-continuity
assertions. It does not assert joint uniform continuity of multiplication.

`IdempotentedRingTopologyTheorem` is the single closed target at the
arbitrary ring universe. For every nonunital ring it asserts the uniform
additive-group and uniform left-multiplication laws. Under the further
premise `IsIdempotented A` it asserts coordinate separation, the Hausdorff
law, uniform right multiplication, and the topological-ring law. These
are conclusions rather than certificate inputs. Complete unapplied
interfaces and definitional local-structure formulas check the intended
parameters and the actual structures. No unit, nontriviality,
commutativity, countability or finiteness premise is added. In particular,
zero rings and zero idempotents remain included.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The read passages are I.1.1–I.1.3, printed pp.6–9/PDF12–15. Printed p.6
specifies the nonunital convention and corner order. Printed p.7 gives
finite local units. Printed p.8 constructs the right-annihilator
neighborhoods, their additive translates and the corresponding
uniformity. Printed p.9 asserts injectivity of the map with coordinates
`a ↦ a * e`.

These six targets are internal intrinsic laws of that actual source
construction. The uniform-group and topological-ring class formulations
are not separate labeled results in Renard. Coordinate separation makes
the source injectivity assertion explicit, and the Hausdorff target
expresses its consequence for the actual coordinate uniformity. The
multiplication laws are further intrinsic consequences of distributivity,
associativity and the source local-unit property; no such consequence is
assumed as part of the uniformity construction. The parent retains their
proof obligation through an exact proof successor.

The prerequisite is imported by its published Lean module name,
`Langlands.Algebra.IdempotentedRingUniformity`. This pair introduces no
replacement of its uniformity or of the original ring operations. The source
pages were read directly, including visual checks of PDF14–15. No
source-specific project errata note was present when this pair was prepared.
Mathlib's class definitions were checked in
`Mathlib.Topology.Algebra.IsUniformGroup.Defs` and
`Mathlib.Topology.Algebra.Ring.Basic`; their exact class packaging is internal
formalization provenance.

This is statement coverage only. It proves none of the six targets and
asserts no inverse-limit topology, density, completeness, completion
multiplication, direct-sum/quotient comparison or extended module action.
Those remain separate obligations of the whole-book program.
