# The canonical etale quotient of a smooth algebraic-space relation

Worker 712 proves
`Langlands.AlgebraicGeometry.AlgebraicSpace.smoothRelationQuotient.{u}`. Its
type is exactly the published `SmoothRelationQuotientStatement.{u}` (Worker 59).
Worker 303 contributed to the decomposition. The statement and its import
closure are unchanged.

## The implemented proof

The proof is one term. It applies the published reduction
`SmoothRelationQuotient.smoothRelationQuotientStatement_of` (module
`SmoothRelationQuotientReduction`) to proofs of its four prerequisite
statements. All four proofs are published Library theorems:

- P1, `monomorphismLocallyFiniteTypeScheme :
  MonomorphismLocallyFiniteTypeSchemeStatement.{u}` (module
  `AlgebraicSpace.MonomorphismLocallyFiniteTypeSchemeProof`). An algebraic
  space with a monomorphism into a scheme `Y` is represented by a scheme if
  it has an etale surjective scheme atlas whose map to `Y` is locally of
  finite type.
- P2, `smoothEquivalenceRelationEtaleSlice :
  SmoothEquivalenceRelationEtaleSliceStatement.{u}` (module
  `SmoothEquivalenceRelationEtaleSliceProof`). A scheme equivalence relation
  with smooth projections has an etale slice `g : U' ⟶ U`, locally of finite
  type, for which `pullback.snd g t ≫ s` is etale and surjective.
- P4, `smoothEtaleSourceDescent : SmoothEtaleSourceDescentStatement.{u}`
  (module `SmoothEtaleSourceDescentProof`). Smoothness of a scheme morphism
  can be checked after precomposing with an etale surjection.
- D3, `etaleEquivalenceRelationAlgebraicSpaceQuotient :
  EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u}` (module
  `EtaleEquivalenceRelationAlgebraicSpaceQuotientProof`). An etale
  equivalence relation of schemes over `S` has an algebraic-space quotient
  with an etale surjective map from its object scheme whose kernel pair is
  the relation.

The reduction's Markdown describes how these combine. P1 shows that the
arrow space `R` is a scheme. P4 shows that its projections are smooth
scheme morphisms. P2 gives an etale slice `U'`, and the restricted relation
`R'` on `U'` is an etale equivalence relation. D3 gives its quotient. The
recognition isomorphism `quotientSheafIsoOfPresentation`
(`SmoothRelationQuotientComparison`) identifies that quotient with the
canonical quotient sheaf. Smoothness and surjectivity of the quotient map
then descend along the etale surjective presentation.

## Provenance

The route follows the smooth case of Stacks Project Theorem 80.10.1 (Tag
04S6) and Section 80.12 (Tag 076L), as cited by the statement's Markdown.
This unit adds no mathematics beyond the application of the reduction.
