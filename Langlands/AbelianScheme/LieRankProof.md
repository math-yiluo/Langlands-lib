# Local freeness and relative-dimension rank of abelian-scheme Lie modules

For every scheme `S : AlgebraicGeometry.Scheme.{u}` and actual abelian scheme
`A : Langlands.AbelianScheme S`, the theorem
`Langlands.AbelianScheme.lieLocalFreenessRank` proves the existing
`LieLocalFreenessRankStatement A`. Thus the constructed `A.Lie` is both locally
free and of finite type, and, for every natural number `g`, the geometric
hypothesis `A.HasRelativeDimension g` implies that `A.Lie` is locally free of
rank `g`.

The proof uses the actual definition
`A.Lie = dual(cotangentAtIdentity A.toGrp)`, where the cotangent module is the
pullback of `relativeDifferentials A.X.hom` along
`Langlands.GroupScheme.identitySection A.toGrp`. The statement and these
constructions are imported unchanged.

## Implemented proof

Apply `Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank` to the
structure morphism `A.X.hom`. Its first clause, using `A.smooth`, supplies one
local-generators datum with both local freeness and finite type. Apply
`Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank` along the identity
section, then `Langlands.Scheme.Modules.dualFiniteLocalBasisRank` to the
cotangent module. The resulting datum `q` supplies both Mathlib predicates
`SheafOfModules.IsLocallyFree A.Lie` and `SheafOfModules.IsFiniteType A.Lie`.

For a given `g` and `A.HasRelativeDimension g`, apply the rank clause of the
same smooth-differentials theorem, followed by the rank clauses of pullback
and dual preservation. Definitional unfolding identifies the resulting
module with `A.Lie` and the geometric hypothesis with Mathlib
`SmoothOfRelativeDimension g A.X.hom`.

No fixed global relative dimension is needed for the finite local freeness
assertion. The rank assertion is conditional on each specified relative
dimension; it does not assert uniqueness of rank on an empty base.

## Provenance

This is an internal derived proof by Worker 309, composing the published
smooth-differentials, pullback, and internal-dual finite-local-basis theorems
named above. It adds no hypotheses beyond an arbitrary scheme and its abelian
scheme. The geometric source derivation belongs to the unchanged
[target statement](LieRankStatement.md); this file describes the implemented
Lean proof.
