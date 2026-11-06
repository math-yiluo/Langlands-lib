# A parabolic contains a maximal torus of the ambient group

Authors: Worker 1336 and Worker 1340.

`Langlands.GroupScheme.parabolicMaximalTorus` proves exactly the published
`Langlands.GroupScheme.ParabolicMaximalTorusStatement.{u}`. For every field
`k : Type u`, connected reductive group scheme `G` over `Spec k`, and
parabolic inclusion `i : P ⟶ G`, it gives a commutative group scheme `T`
and maps `j : T.toGrp ⟶ G` and `f : T.toGrp ⟶ P` with
`IsMaximalTorus j` and `f ≫ i = j`. These objects and maps are over the
original field. Maximality is in `G`. The theorem adds no premise to the
published proposition and applies to imperfect fields and arbitrary
characteristic. It does not require the torus to be split.

## Implemented proof

The proof applies `parabolicMaximalTorus_of_structuralInputs` from
[ParabolicMaximalTorusReduction](ParabolicMaximalTorusReduction.md) and
supplies all six structural inputs with published theorems:

- `maximalTorusExistence`, from `Torus.ExistenceProof`, gives a maximal
  torus of every smooth affine group over the original field.
- `maximalTorusBaseChange`, from `Torus.MaximalBaseChangeProof`, proves
  the equivalence of maximality before and after any field extension.
- `borelMaximalTorus`, from `Absolute.BorelMaximalTorusProof`, gives an
  ambient maximal torus inside any Borel over an algebraically closed field.
- `borelContainingSubgroupConnectedStatement`, from
  `Absolute.BorelContainingSubgroupConnected`, proves connectedness of a
  smooth closed subgroup containing a Borel of a smooth connected affine
  group over an algebraically closed field.
- `maximalTorusConjugacy`, from `Absolute.MaximalTorusConjugacyProof`, gives
  conjugacy inside any smooth connected affine group over an algebraically
  closed field. The adapter
  `subgroupConjugate_iff_exists_commGroupSchemeIso` converts its commutative
  source isomorphism to the reduction's underlying group-scheme conjugacy
  predicate, preserving the rational point and the morphism equation.
- `IsConnectedReductive.connectedSpace_toAlgebraicClosure`, from
  `GeometricConnectedness`, gives the connectedness of the ambient group
  after extension to the algebraic closure.

All module names above have prefix `Langlands.GroupScheme`. The last two
inputs are supplied by lambdas specializing the named theorems to the
reduction's arguments. Every structural input is discharged.

The imported reduction first makes the parabolic affine using its closed
embedding into the affine group `G`. Rational maximal-torus existence
chooses `f : T.toGrp ⟶ P`, and the ambient map is `j = f ≫ i`, so the
factorization equation is reflexive. Over the algebraic closure, the
parabolic's defining Borel factorization and the containing-Borel theorem
make the parabolic connected. The chosen torus remains maximal in that
parabolic by base-change invariance. The Borel contains a torus maximal
in the ambient group. Conjugacy of maximal tori inside the extended
parabolic, through `MaximalToriAreConjugate.isMaximalTorus_comp`, therefore
makes the chosen torus ambient-maximal after extension. The reverse
implication of base-change invariance gives ambient maximality over `k`.
The construction works also for the full-group parabolic and when `G`
is itself a torus.

## Provenance

This file is an internal composition of the named published proofs. It
finishes the derived formulation documented in
[ParabolicMaximalTorusStatement](ParabolicMaximalTorusStatement.md), which
cites J. S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The converse proof of Theorem 25.1, printed p.544 (one-based PDF p.560),
uses a maximal torus contained in the parabolic. The structural route
above uses Theorem 17.82 and Corollary 17.83, printed p.379 (PDF p.395),
the paragraph after Definition 17.12, printed p.355 (PDF p.371),
Corollary 17.49, printed p.367 (PDF p.383), and Theorem 17.10,
printed pp.354–355 (PDF pp.370–371). The paired Markdown of each imported
proof explains its actual construction and source comparison. The exact
target and its imported Lean/Markdown pairs are preserved.
