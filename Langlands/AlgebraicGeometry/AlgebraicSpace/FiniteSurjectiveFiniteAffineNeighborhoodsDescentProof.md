# Proof of finite-surjective descent of finite-set affine neighborhoods

Author: Worker 5045.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveFiniteAffineNeighborhoodsDescentProof`.

## Statement

`finiteSurjectiveFiniteAffineNeighborhoodsDescent :
FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement.{u}`
proves the published statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement`
with no added hypotheses. Take any commutative ring `R : Type u`. Let `Y` be a
quasi-compact, quasi-separated algebraic space over `Spec R`, and let `f : U ⟶ Y` be a finite,
geometrically surjective map. Here `U` is a scheme over `Spec R` in which every finite set of
points lies in an affine open (an AF scheme). Then `Y` is represented by an AF scheme over
`Spec R`, through a natural isomorphism on all scheme tests over `Spec R`.

This is the descent direction of Philipp Gross, *Tensor generators on schemes and stacks*
(Algebraic Geometry 4 (2017)), Theorem 1.2, specialized to an affine base. The statement's
Markdown describes the specialization and its source passages.

## Proof

The theorem applies one published theorem to another, and adds no new argument:

1. `AFDescentFiniteSets.finiteAffineNeighborhoodsDescent_of_quasiAffineSourceAF` (module
   `AFDescentFiniteSets`) proves
   `FiniteSurjectiveQuasiAffineSourceAFStatement → FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement`.
   It is Gross's reduction to a quasi-affine source (Corollary 3.8 and the proof of Theorem 1.2).
   Given the quasi-affine-source case, it represents `Y` by gluing AF models of quasi-compact
   open subspaces of `Y` (module `AFDescentOpenCharts`). Each such subspace has a quasi-affine
   inverse image in `U`. It then shows that any representing scheme is AF: a finite point set
   has a compact open neighborhood with an AF model, and an affine open of that model
   containing the set maps onto an affine open of the representing scheme. Everything stays
   over the original base `Spec R`.
2. `finiteSurjectiveQuasiAffineSourceAF` (module `FiniteSurjectiveQuasiAffineSourceAFProof`)
   proves `FiniteSurjectiveQuasiAffineSourceAFStatement` with no premises. That is Gross's
   Proposition 3.5 for a finite surjection with quasi-affine source over an affine base. Its
   proof combines the reduced closed subspace theorem, the Noetherian case by Noetherian
   induction, and Noetherian approximation.

The theorem applies 1 to 2. The Markdown of each cited module describes its proof. The proof
uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
