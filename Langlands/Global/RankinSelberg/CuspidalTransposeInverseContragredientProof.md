# The dual cusp forms lie in a cuspidal contragredient

`cuspidalTransposeInverseContragredient` proves the exact Library
`CuspidalTransposeInverseContragredientStatement.{u}` at the free
number-field universe `u`. The statement records the correspondence to
Cogdell (2004), pp. 201, 203 and 206–207.
[Statement and source correspondence](CuspidalTransposeInverseContragredientStatement.md)

The proof applies `cuspidalLocalGKTransposePairingReduction` to
`Archimedean.archimedeanTransposePairing` in the same universe. The
latter supplies nonzero inverse-transpose bilinear forms for every
irreducible admissible real or complex GK module. The reduction applies
them to the actual local source models of each cuspidal realization.
It assembles them with the finite adelic form, which comes from
nonarchimedean Gelfand–Kazhdan and restricted tensor factorization.
[Archimedean pairing proof](../../Representation/Archimedean/TransposePairingProof.md),
[local-to-global reduction](CuspidalLocalGKTransposePairingReduction.md)

The assembled nonzero form and the cuspidal invariant-pairing criterion
give `IsContragredientOf T.transpose.realization T.realization`.
The witness for each `x : T.Space` is `T.transposeEquiv x`, whose cusp
function is exactly `dualFunction F (r + 1) (cuspFunction F T x)`.
[Nonzero-pairing reduction](CuspidalNonzeroTransposePairingReduction.md)
