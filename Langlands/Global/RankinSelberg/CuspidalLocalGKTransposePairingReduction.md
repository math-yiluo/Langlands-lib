# Exact cuspidal transpose reduction from local archimedean GK forms

This internal conditional intermediate proves
`CuspidalLocalGKTransposePairingReductionStatement`, whose conclusion is
exactly the unchanged
`CuspidalTransposeInverseContragredientStatement` at the free number-field
universe `u`.

Its sole premise is the published
`Langlands.Archimedean.ArchimedeanTransposePairingStatement.{u}`. This
is the conjunction of `RealTransposePairingStatement` and
`ComplexTransposePairingStatement`, both local existence propositions,
proved in the Library (`Archimedean.archimedeanTransposePairing`, module
`TransposePairingProof`). They assert nonzero inverse-transpose bilinear forms for
every irreducible admissible genuine real or complex GK-module of
positive matrix rank, without genericity or unitarity assumptions.

For each actual cuspidal realization, the preceding construction
`T.placeDensityModels` chooses actual local irreducible admissible
subspaces. Their restricted actions satisfy the genuine local GK axioms.
The proved density hypotheses include exactly the irreducibility and
admissibility needed by each local statement. Apply the real statement
at every real place and the complex statement at every complex place,
with matrix rank `r + 1` and the actual source carrier in universe `u`.
This proves the chosen-model form premise of
`cuspidalArchimedeanModelPairingReduction`.

That implemented reduction already discharges the finite adelic form
existence and all actual finite/infinite and all-place assembly. Its
nonzero intrinsic form identifies the actual cuspidal transpose
realization as a contragredient, and the existing actual vector
comparison supplies precisely every target `dualFunction` cusp form.
Composition therefore gives the displayed exact global conclusion
from the two named local existence propositions only.

The provenance is internal application and composition of the proved
source-model properties and global assembly with the published local
statement interface. No local existence proof is supplied or assumed
proved here. This conditional result does not establish the
unconditional global target; `cuspidalTransposeInverseContragredient`
(module `CuspidalTransposeInverseContragredientProof`) applies it to
`Archimedean.archimedeanTransposePairing` and so proves it.
