# Descent of a Frobenius-invariant geometric Borel

For a finite field `k : Type u` and a group scheme `G` affine over `Spec k`,
`IsBorelSubgroup.descentOfFrobenius` constructs an actual ground-field geometric
Borel from a prescribed algebraic-closure Borel whose range agrees with the
range of its canonical arithmetic Frobenius translate on every relative test
scheme. Its result is `GeometricBorelDescentData`: an affine ground-field group,
its geometric Borel inclusion in `G`, an isomorphism recovering the original
source over the algebraic closure, and the exact inclusion recovery equation.
No finite model of the geometric Borel is supplied or assumed.

The algebraic closure of a finite field is Galois over the original field.
The general infinite-Galois closed-subgroup descent theorem
`Descent.GaloisInvariantClosedSubgroup.overlap_range_eq_of_frobenius` therefore
converts the given Frobenius range equality to equality on the full canonical
fpqc overlap. The published `IsBorelSubgroup.descentOfOverlap` constructs the
descended closed subgroup and reflects the geometric Borel property.

`IsBorelSubgroup.descentOfFrobeniusTransport` gives the same construction when
the invariance hypothesis is written using the published canonical
`SubgroupFunctor.galoisTransport` action. The two
`isQuasiSplit_of_borel_frobenius...` theorems package the result as quasi-splitness
when the ambient group is connected reductive.

Worker 1611 derived these adapters from the imported descent results. This
unit assumes a specified Borel and its full all-test Frobenius invariance.
Constructing such a Borel, including the geometric Borel existence, conjugacy
and Lang step, remains an obligation of the finite-field quasi-splitness proof.
This unit does not assert the unconditional quasi-splitness or solvability
targets.
