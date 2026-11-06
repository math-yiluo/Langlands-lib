# A connected group variety without tori is unipotent

Author: Worker 1487.

`Langlands.GroupScheme.noTorusUnipotent` proves the exact published
`Langlands.GroupScheme.NoTorusUnipotentStatement.{u}`. For any field
`k : Type u` and smooth connected affine group scheme `Q` over `Spec k`,
suppose every homomorphism `g : T.toGrp ⟶ Q` from a commutative group
scheme with `IsTorus T.toGrp` has `SubgroupFunctor.range g = ⊥`.
Then `IsUnipotent Q`.

Only tori over the original field occur in the hypothesis. The conclusion
retains arbitrary universe and characteristic, including finite and imperfect
fields, with no additional premise. The published target pair and its imports
are unchanged.

## Implemented proof

This file is an internal composition of published Library proofs. It applies
`noTorusStructuralReduction` from `Torus.NoTorusStructuralReductionProof`
and supplies all six structural arguments, in order:

1. `nilpotentCentralTorus`, from `Nilpotent.NoTorusUnipotent`;
2. `finiteFieldGeometricMaximalTorus`, from
   `Torus.FiniteFieldGeometricMaximalProof`;
3. `algClosedTrivialMaximalTorusUnipotent`, from
   `Absolute.NoCocharacterUnipotent`;
4. `Lie.semisimpleCentralizerSmooth`, from
   `Lie.SemisimpleCentralizerSmooth`;
5. `Lie.semisimpleCentralizerSpanning`, from
   `Lie.SemisimpleCentralizerSpanningProof`;
6. `semisimpleIsogenyReduction`, from `Lie.SemisimpleIsogenyReduction`.

Each argument proves its named proposition at the same arbitrary universe.
No structural proposition remains as an outer hypothesis.

The structural reduction first converts triviality of all torus
homomorphisms into absence of nontrivial closed tori. For a finite ground
field, geometric maximal-torus existence gives an actual torus inclusion
maximal both over the field and over its algebraic closure. The absence
hypothesis and the algebraically closed trivial-maximal-torus theorem then
give unipotence. The finite-field existence proof independently uses
maximal-torus conjugacy, Lang's construction and Frobenius descent.

For an infinite ground field, the reduction uses strong induction on Lie
dimension. The isogeny reduction supplies a smooth connected affine target
and lifts its closed tori up to torus isogeny, so it inherits absence of
closed tori. In the nilpotent case, nilpotence reflects along the finite
homomorphism to the original group, and the central-torus theorem gives
unipotence. Otherwise, semisimple descent supplies a ground-field tangent
element with proper centralizer. Its smooth centralizer's identity component
has smaller Lie dimension and inherits absence of closed tori, so induction
makes it unipotent. The nonzero semisimple tangent element contradicts that
unipotence through the published centralizer nonunipotence adapter.

The detailed constructions and provenance belong to the named imported
proof pairs. This final composition adds no new geometric construction.
