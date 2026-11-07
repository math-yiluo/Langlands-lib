# AF representability from a finite surjection with Noetherian quasi-affine source

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianSchemeQuasiAffineSourceAFStatement`,
namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`. It imports the published
`FiniteSurjectiveQuasiAffineSourceAFStatement` for the existing predicates, and Mathlib's
`Mathlib.AlgebraicGeometry.Noetherian`.

## Statement

`NoetherianSchemeQuasiAffineSourceAFStatement.{u}` is the following proposition. Take a scheme
`S : Scheme.{u}`, a scheme `U : Over S`, an algebraic space `Y : AlgebraicSpace S` and a
morphism `f : (schemeToSpace S).obj U ⟶ Y`. Assume:

- `Y` is quasi-compact (`IsQuasiCompact Y`) and quasi-separated over `S` (`IsQuasiSeparated Y`);
- the scheme `U.left` is quasi-affine (Mathlib's `IsQuasiAffine`);
- the scheme `U.left` is Noetherian, in Mathlib's sense `AlgebraicGeometry.IsNoetherian`:
  locally Noetherian and quasi-compact;
- `hom f` is finite and surjective (`IsFinite`, `IsSurjective`).

Then there is a scheme `P : Over S` such that every finite set of points of `P.left` lies in an
affine open (`PointTopology.HasFiniteAffineNeighborhoods`), together with a natural isomorphism
`(schemeYoneda S).obj P ≅ Y.presheaf` of presheaves on all schemes over `S`.

## Relation to the source and provenance

Derived. This is the published `FiniteSurjectiveQuasiAffineSourceAFStatement` with two changes:

- the base `Spec R` is replaced by an arbitrary base scheme `S`;
- the hypothesis that `U.left` is a Noetherian scheme is added.

All other hypotheses and the conclusion are the same as in that statement. Its Markdown
explains the correspondence with Gross, *Tensor generators on schemes and stacks*,
Proposition 3.5 (source `gross-tensor-generators-schemes-stacks-2017`, printed p. 510 /
PDF p. 10).

In Gross's proof, Step 3 (printed p. 511 / PDF p. 11) uses Noetherian approximation to reduce
to `X` of finite type over `ℤ`, where a Noetherian induction runs. This statement isolates
that situation for the source. The quasi-affine finite-type models produced by approximation
are Noetherian schemes.

The statement replaces the published `NoetherianQuasiAffineSourceAFStatement`, which only
assumes that the underlying topological space of `U.left` is Noetherian. With the scheme
hypothesis, the schemes finite over `U` that the induction uses are again Noetherian
(Mathlib's `LocallyOfFiniteType.isLocallyNoetherian`). The reduction of the general statement
to this case is `QuasiAffineSourceAFNoetherianSchemeApproximationStatement`.
