# AF representability from a finite surjection with Noetherian quasi-affine source

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianQuasiAffineSourceAFStatement`,
namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`. It imports
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFStatement` for
the existing predicates.

## Statement

`NoetherianQuasiAffineSourceAFStatement.{u}` is the proposition below. Fix

- a scheme `S : Scheme.{u}`, a scheme `U : Over S` and an algebraic space
  `Y : AlgebraicSpace S`;
- a morphism `f : (schemeToSpace S).obj U ⟶ Y`.

Assume:

- `Y` is quasi-compact (`IsQuasiCompact Y`) and quasi-separated over `S`
  (`IsQuasiSeparated Y`);
- the scheme `U.left` is quasi-affine (Mathlib's `IsQuasiAffine`);
- its underlying topological space is Noetherian (`TopologicalSpace.NoetherianSpace`);
- `hom f` is finite and surjective (`IsFinite`, `IsSurjective`).

Then there is a scheme `P : Over S` such that every finite set of points of `P.left` lies in an
affine open (`PointTopology.HasFiniteAffineNeighborhoods`), together with a natural isomorphism
`(schemeYoneda S).obj P ≅ Y.presheaf` of presheaves on all schemes over `S`.

## Relation to the source and provenance

Derived. This is the published `FiniteSurjectiveQuasiAffineSourceAFStatement` with two changes:

- the base `Spec R` is replaced by an arbitrary base scheme `S`;
- the hypothesis that `U.left` is a Noetherian topological space is added.

Every hypothesis and the conclusion are otherwise the same as in that statement, whose Markdown
explains the correspondence with Gross, *Tensor generators on schemes and stacks*,
Proposition 3.5 (source `gross-tensor-generators-schemes-stacks-2017`, printed p. 510 /
PDF p. 10). In Gross's proof, Noetherian approximation (Step 3, printed p. 511 / PDF p. 11)
reduces to a Noetherian situation in which a Noetherian induction on closed subspaces runs.
This statement isolates that situation. Topological Noetherianity of the source is what such
an induction on closed subsets of `|Y|` uses: `|Y|` is then a continuous image of a Noetherian
space. The reduction of the general statement to this case is the separate statement
`QuasiAffineSourceAFApproximationStatement`.
