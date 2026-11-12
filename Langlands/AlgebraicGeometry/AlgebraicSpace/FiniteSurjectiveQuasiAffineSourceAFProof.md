# Proof of AF representability from a finite surjection with quasi-affine source

Author: Worker 5067.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFProof`.

## Statement

`finiteSurjectiveQuasiAffineSourceAF : FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`
proves the published statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFStatement`
with no added hypotheses. For every commutative ring `R : Type u`, let `Y` be a quasi-compact,
quasi-separated algebraic space over `Spec R` and `f : U ⟶ Y` a finite surjective map from a
quasi-affine scheme `U` over `Spec R`. Then `Y` is represented, by a natural isomorphism on all
scheme tests over `Spec R`, by a scheme over `Spec R` in which every finite set of points lies
in an affine open.

This is a specialization of Philipp Gross, *Tensor generators on schemes and stacks*
(Algebraic Geometry 4 (2017)), Proposition 3.5, to a finite surjection with quasi-affine source.
The statement's Markdown describes the specialization.

## Proof

The proof composes three published theorems:

1. `ReducedClosedSubspace.reducedClosedSubspace` (module `ReducedClosedSubspaceProof`) proves
   `ReducedClosedSubspaceStatement`. Let `f : U ⟶ Y` be a finite surjection onto a
   quasi-compact quasi-separated algebraic space and `j : U_T ⟶ U` a closed immersion from a
   reduced scheme with saturated range. Then some quasi-compact quasi-separated algebraic space
   `Y_T` receives a finite surjection `f_T : U_T ⟶ Y_T`, and two points of `U_T` have the same
   image under `f_T` exactly when their images in `U` have the same image under `f`.
2. `noetherianSchemeQuasiAffineSourceAF_of_reducedClosedSubspace` (module
   `TupleOrbitInduction`) proves
   `ReducedClosedSubspaceStatement → NoetherianSchemeQuasiAffineSourceAFStatement`. This is the
   Noetherian case of Gross's Proposition 3.5, over any base scheme and with a Noetherian
   quasi-affine source. Its proof is a Noetherian induction on closed subsets of the source.
3. `quasiAffineSourceAFNoetherianSchemeApproximation` (module
   `QuasiAffineSourceAFNoetherianSchemeApproximationProof`) proves
   `NoetherianSchemeQuasiAffineSourceAFStatement → FiniteSurjectiveQuasiAffineSourceAFStatement`.
   This is Gross's Step 3, "By approximating `X` and `p`, we may assume that `X` is of finite
   type over `Z`", implemented by absolute Noetherian approximation of an étale presentation of
   the finite cover.

The theorem applies 3 to the result of applying 2 to 1. Each module's Markdown describes its
proof.
