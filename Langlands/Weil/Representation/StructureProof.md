# Complete representation structure

`Langlands.Weil.representationStructure.{uW, uV}` proves exactly the published
`Langlands.Weil.RepresentationStructure.{uW, uV}` from
[Structure](Structure.md). Its complete unapplied type is

```lean
Langlands.Weil.representationStructure.{uW, uV} :
  Langlands.Weil.RepresentationStructure.{uW, uV}
```

The group universe `uW` and representation-carrier universe `uV` are
independent. There are no additional term parameters or hypotheses.

## Implemented proof

The published proposition unfolds to
`UnramifiedReduction.{uW, uV} ∧ FiniteImageExtension.{uW, uV}`.
The proof applies conjunction introduction, using the published theorem
`unramifiedReduction.{uW, uV}` for the first clause and
`finiteImageExtension.{uW, uV}` for the second. Both component theorems
are imported by module name and applied at the same two independent universes.

The first component retains the general commuting unramified correction,
the irreducible scalar-twist reduction, and the irreducible finite-order
determinant criterion. Its hypotheses remain those of the generic integer
extension with open, compact, nonarchimedean degree kernel. The second
component retains the equivalence between finite image and existence of a
unique continuous extension from the actual integer pullback to its compact
Hausdorff nonarchimedean ambient group. The aggregate preserves both clauses
in their original order, including every quantified hypothesis and conclusion.
The statement pair and all imported inputs are unchanged.

## Internal provenance and scope

This is an internal packaging proof of the existing conjunction. Its
mathematical provenance is inherited from the published
[unramified reduction proof](UnramifiedReductionProof.md) and
[finite-image extension proof](FiniteImageExtensionProof.md), together with
the source correspondence in [Structure](Structure.md). The conjunction
step introduces no further source-dependent mathematical claim.

Worker 32 authored this aggregate. The imported reduction was developed by
Workers 32 and 66, and the imported extension by Worker 18; those contributions
remain in their existing modules. This proof establishes the generic
`RepresentationStructure` target. The actual-local specialization, local
reciprocity, and the local Langlands correspondence remain outside its scope.
