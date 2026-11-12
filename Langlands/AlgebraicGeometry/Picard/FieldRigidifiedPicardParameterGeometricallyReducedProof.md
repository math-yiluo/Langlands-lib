# Geometric reducedness of an actual universal rigidified Picard parameter

`Langlands.AbelianScheme.fieldRigidifiedPicardParameterGeometricallyReduced`
proves exactly
`Langlands.AbelianScheme.FieldRigidifiedPicardParameterGeometricallyReducedStatement.{u}`.
The universe `u` is arbitrary. For any field `k`, actual abelian scheme `A`
over `Spec k`, parameter `P : Over (Spec k)` and actual rigidified family
`L : RigidifiedFamily A P`, all-test universality of `L` and
`LocallyOfFiniteType P.hom` imply Mathlib's `GeometricallyReduced P.hom`.
The field may be imperfect and need not be algebraically closed.

## Implemented proof

The proof is a composition of three published results:

- `Langlands.AlgebraicGeometry.geometricallyReducedOfAlgClosed`, from
  `Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof`;
- `Langlands.AbelianScheme.rigidifiedUniversalBaseChange`, from
  `Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBaseChangeProof`;
- `Langlands.AbelianScheme.algClosedFieldRigidifiedPicardParameterReduced`,
  from
  `Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardParameterReducedProof`.

Install the supplied local finite type hypothesis as a local instance.
The first theorem reduces geometric reducedness to reducedness of
`Limits.pullback P.hom b` for every algebraically closed field `K : Type u`
and every morphism `b : Spec K ⟶ Spec k`.

For such `b`, use the actual base-changed abelian scheme
`(baseChange b).obj A`, parameter `(Over.pullback b).obj P`, and family
`(baseChangeFamily b A P).obj L`. The second theorem transports the
supplied universal property to this family, retaining universality on all
test schemes, including nonreduced schemes.

The structure morphism of the new parameter is definitionally
`Limits.pullback.snd P.hom b`. Mathlib's stability of local finite type
under base change supplies its local finite type instance. The third
theorem therefore proves reducedness of the new parameter's carrier,
which is the required pullback scheme.

The testing theorem handles arbitrary field base changes by passing to
their algebraic closures and descending reducedness along the resulting
flat surjective projections. Its proof and companion contain that descent
argument; this module uses the published conclusion directly. All schemes
and fields in the present assembly stay in the same arbitrary universe.

## Provenance and scope

Worker 2391 wrote this derived assembly and its explanation, completing
the earlier private conditional reduction with the published algebraically
closed reducedness theorem. The new content is the composition above.
The mathematical provenance and proofs of the three imported results
remain in their published companions. This module makes no independent
claim about the original literature's proof route.

The final theorem has exactly the published statement as its type, with
no additional premise. It asserts no existence of a universal parameter.
It neither uses an identity-component smoothness proof nor edits any
published statement or dependency.
