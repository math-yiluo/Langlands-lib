# Reduction of quasi-affine-source AF representability to Noetherian sources

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineSourceAFApproximationStatement`,
namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`. It imports
`Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianQuasiAffineSourceAFStatement`, which in
turn imports the published `FiniteSurjectiveQuasiAffineSourceAFStatement`.

## Statement

`QuasiAffineSourceAFApproximationStatement.{u}` is the implication

`NoetherianQuasiAffineSourceAFStatement.{u} → FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`.

The hypothesis is the case of AF representability with a quasi-affine source whose underlying
space is Noetherian, over every base scheme in universe `u`. The conclusion is the published
statement over `Spec R` for every commutative ring `R : Type u`, with no Noetherian
hypothesis.

## Mathematical content and provenance

Derived. This isolates the approximation part of the proof of Gross, *Tensor generators on
schemes and stacks*, Proposition 3.5 (source `gross-tensor-generators-schemes-stacks-2017`).
In Step 3 of that proof (printed p. 511 / PDF p. 11) Gross writes: "By approximating `X` and
`p`, we may assume that `X` is of finite type over `Z`." He then refers to the reduction step
in the proof of Rydh's Chevalley theorem.

The proposition is an implication between two published-form statements; it asserts nothing
beyond what the literature's reduction asserts. It is true by the following argument, which
is not part of this statement:

1. Approximate `Y` (absolutely, over `Spec ℤ`) by an algebraic space `Y₁` of finite type over
   `ℤ`, together with an affine morphism `Y ⟶ Y₁`.
2. Approximate the finite surjective quasi-affine cover by a finite surjective cover of `Y₁`
   by a quasi-affine scheme of finite type over `ℤ`, which has a Noetherian underlying space.
3. Apply the hypothesis over the absolute base.
4. Use that an algebraic space affine over an AF scheme is represented by an AF scheme.
5. Transport the representer and the natural isomorphism back to `Spec R`.

The Library contains the absolute Noetherian approximation of presentations (published
`EtaleEquivalenceRelationNoetherianFirstLevelStatement` and
`EtaleEquivalenceRelationNoetherianCoverLevelStatement`, the latter for covers with affine
quotient), on which a proof can build.
