# The flag step of Chevalley's Borel-intersection theorem

Authors: Workers 1489 and 1460.

`Langlands.GroupScheme.unipotentTorusBorelsToAllBorels` proves exactly
`Langlands.GroupScheme.UnipotentTorusBorelsToAllBorelsStatement.{u}` from
`Absolute.ChevalleyUnipotentEnvelopeSteps`, at arbitrary universe `u`.
For an algebraically closed field `k`, a smooth connected affine group scheme
`G`, a maximal torus embedding `t : T.toGrp ⟶ G`, and a smooth connected
unipotent closed subgroup `i : U ⟶ G`, containment of `U` in every Borel
containing `T` implies containment of `U` in every Borel of `G`.
Every containment is an inclusion of range subgroup functors on every test
scheme. The theorem retains all the published hypotheses and has no further
premise. In particular, it applies to nonreductive `G` and does not require
`T` to normalize `U`.

## Implemented proof

The proof instantiates the four inputs of the published theorem
`unipotentTorusBorelsToAllBorels_of_geometric_inputs` in
`Absolute.FlagStepReduction`.

The first three inputs are the unconditional published theorems
`someBorelQuotientProper` from `Absolute.BorelProperQuotientProof`,
`flagInvariantAffineOpenCover` from
`Absolute.FlagInvariantAffineOpenCoverProof`, and `borelConjugacy` from
`Absolute.BorelConjugacyProof`. They supply, respectively, a Borel whose
actual quotients are proper, invariant affine neighbourhoods of every
rational point of the supplied Borel quotient, and rational conjugacy of
Borel embeddings. The cover concerns the actual restricted scheme action:
invariance is equality of inverse-image scheme opens under the action and
the second projection.

The remaining input asks for all-test fixedness of every rational point
under a smooth connected affine unipotent group acting on a proper scheme
with the stated invariant affine neighbourhoods. The lambda introduces
these data, installs the supplied properness proof as an instance, and
applies
`SchemeAction.isFixed_of_invariantAffineNeighborhoods_of_kostantRosenlicht`
from `SchemeActionProperFixedFromKR`. Its Kostant–Rosenlicht input is the
unconditional theorem `unipotentAffineOrbitClosed` from
`UnipotentAffineOrbitClosedProof`.

The imported fixedness argument first uses Kostant–Rosenlicht and the
invariant affine neighbourhoods to keep each orbit closure inside an
invariant affine neighbourhood of its original rational point. The reduced
equivariant orbit closure is proper and has a closed immersion into that
affine neighbourhood, so it is affine and hence finite over the field.
It has finitely many rational sections. The connected smooth finite-target
action theorem fixes the lifted section on every test scheme, and
equivariance carries this fixedness to the original section. The proper
ambient scheme need not be reduced.

The reduction constructs an actual smooth quotient by the chosen Borel
and its descended left action. The subgroup `U` is affine because it is a
closed subgroup of affine `G`. Properness and the cover apply to this
quotient, and the fixedness input fixes every rational coset for the
restricted `U` action. The published fixed-quotient containment adapter
uses Borel conjugacy to obtain an actual factor of `i` through each Borel
embedding `b`. Finally, `SubgroupFunctor.range_le_of_factor` gives the
required containment on every test scheme. All four inputs of the
reduction have therefore been supplied by proofs.

## Provenance

This is an internal composition of the named published results. Worker 1460
provided the checked consumer of the geometric reduction and the
Kostant–Rosenlicht fixedness theorem; Worker 1489 supplies the published
cover proof and packages the exact final theorem. The imported reductions
and geometric proofs retain their own authorship and explanations.

The source motivation is Luna's proof in J. S. Milne, *Algebraic Groups*
(2017), Section 17.h, Theorem 17.65 and the following covering argument,
printed pp.374–375 (zero-based PDF pages 389–390), with Kostant–Rosenlicht
Theorem 17.64 on printed pp.373–374. The registered source is
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to this
passage. The published statement explains why Milne's argument for
`I_u(T)` applies to the given `U` using only containment in the Borels
through `T`. The implementation uses the imported reduced-orbit-closure
and finite-target argument described above in place of the source's use
of a solvable fixed point in each orbit closure. This file adds only the
final proof pair and leaves the published target and its imports unchanged.
