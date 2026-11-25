# Reduction to the pairing of the actual cuspidal transpose realization

This internal conditional reduction combines the actual cuspidal transpose
construction (module `Langlands.Automorphic.TransposeOperatorRealization`) with
the pairing transport (`IsTransposeIntertwining.isContragredientOf`) and the cusp
function comparison of `CuspidalTransposeInverseContragredientReduction`. It proves the earlier B1 premise and retains only B2,
`CuspidalTransposePairingStatement`, as an explicit unproved premise. It does
not prove the unconditional `CuspidalTransposeInverseContragredientStatement`.

All statements retain arbitrary universe `u`, every number field `F` with
`CompactSpace (AdeleQuotient F)`, every natural `r`, and every actual cuspidal
operator realization of `GL_(r+1)`.

`cuspidalTransposeEquiv_isTransposeIntertwining` packages the three covariance
identities for the actual `T.transposeEquiv`: finite translations use the
actual adelic inverse transpose, the infinite compact uses `compactTranspose`,
and the genuine real Lie action uses `realLieIota`. The target
`T.transpose` is the actual image realization; its construction preserves
irreducibility for the full operator algebra and cuspidality.

`cuspFunction_transposeEquiv` identifies the cusp function of each transpose
vector with the exact `dualFunction` of the source vector. The continuous
transpose pullback agrees with `ContinuousRationalFunctions.transposeDual`.
The earlier comparison then removes the rational long Weyl element using
rational left invariance. Thus the equality includes the Weyl factor in the
target's definition of the dual function.

`cuspidalTranspose_isContragredientOf_iff` specializes both directions of the
pairing transport criterion to this actual realization. It says precisely that
`T.transpose.realization` is a contragredient of `T.realization` if and only if
the latter has an intrinsic transpose contragredient pairing. This is an
equivalence of obligations, not an existence assertion.

`cuspidalTransposeRealization` proves `CuspidalTransposeRealizationStatement`
by taking `T.transpose` and `T.transposeEquiv` as its witnesses and using the
covariance and continuous-function identities just described.

`CuspidalTransposePairingReductionStatement` is the implication from B2 alone
to the exact Library target. Its theorem `cuspidalTransposePairingReduction`
applies the earlier two-premise reduction to the proved B1 theorem. The retained
B2 premise still requires all finite, compact and real Lie invariance clauses
and a bijection onto all actual contragredient functionals. No archimedean or
surjectivity clause has been removed.

The provenance is internal: the new results compose the actual transpose
construction, the intrinsic pairing criterion and the actual function
comparison. The Library has no proof of B2, the Gelfand--Kazhdan pairing
existence problem, so this module does not prove the target; the Library proves the target by another route
(`cuspidalTransposeInverseContragredient`, module
`CuspidalTransposeInverseContragredientProof`).
