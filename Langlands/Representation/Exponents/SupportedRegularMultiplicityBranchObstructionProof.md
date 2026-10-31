# The supported excess-multiplicity Weyl-branch obstruction

Author: Worker 253, with Worker 514 (first executor of the proof task for
[`GLSupportedRegularMultiplicityBranchObstructionStatement`](SupportedRegularMultiplicityBranchObstructionStatement.md)).

The module `Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionProof`
proves the target statement without hypotheses:

```lean
theorem Langlands.glSupportedRegularMultiplicityBranchObstruction :
    GLSupportedRegularMultiplicityBranchObstructionStatement.{uF, uV, uM, uW}
```

It also proves the intermediate theorem

```lean
theorem Langlands.glSupportedRegularMultiplicityBranchObstruction_of_localization
    (hP2 : GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM})
    (hP2' : GLProductLeviCuspidalLocalizationStatement.{uF, uV, uV}) :
    GLSupportedRegularMultiplicityBranchObstructionStatement.{uF, uV, uM, uW}
```

whose two hypotheses are the product-Levi cuspidal localization of
[`WeylBranchPiecesStatement`](WeylBranchPiecesStatement.md) at two universe
instances. The axioms of both theorems are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

`glSupportedRegularMultiplicityBranchObstruction_of_localization` applies
`glSupportedRegularMultiplicityBranchObstruction_of_pieces` from
[`WeylBranchPiecesAssembly`](WeylBranchPiecesAssembly.md) to these four
pieces:

1. *Geometric-piece lifting* (`GLGeometricPieceLiftingStatement.{uF, uM}`).
   This is `glGeometricPieceLifting_of_upper` from
   [`WeylBranchPieceLiftingFromUpper`](WeylBranchPieceLiftingFromUpper.md),
   applied to the published geometric lemma
   `Geometric.padicGeometricLemma` from
   [`GeometricLemmaProof`](../Geometric/GeometricLemmaProof.md).
2. *Excess branch* (`GLGeometricExcessBranchStatement.{uF, uV, uW}`). This is
   `glGeometricExcessBranch_of_upper` from
   [`GeometricExcessBranchFromUpper`](GeometricExcessBranchFromUpper.md),
   applied to the same geometric lemma.
3. *Product-Levi localization* (`GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM}`).
   This is the hypothesis `hP2`.
4. *Cuspidal constituent* (`GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uV}`).
   This is `glCuspidalInductionJacquetConstituent_of_localization` from
   [`CuspidalInductionJacquetConstituentReduction`](CuspidalInductionJacquetConstituentReduction.md),
   applied to the hypothesis `hP2'`.

`glSupportedRegularMultiplicityBranchObstruction` discharges both hypotheses
with the published theorem
`ProductLeviCuspidalLocalization.glProductLeviCuspidalLocalization` from
[`ProductLeviCuspidalLocalizationProof`](ProductLeviCuspidalLocalizationProof.md),
used once at `.{uF, uV, uM}` and once at `.{uF, uV, uV}`.

The mathematical argument, which follows the branch-selection step of
Silberger 1978, Lemma 5.6, is in
[`WeylBranchPiecesAssembly`](WeylBranchPiecesAssembly.md).
