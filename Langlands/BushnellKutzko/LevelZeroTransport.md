# The unit groups of a principal order in an adapted basis

`stdToAut L b hϖ he` sends a matrix indexed by `Fin f × Fin e` to the
automorphism with that matrix in the adapted basis of `L`.
[Adapted basis](LevelZeroAdaptedBasis.md)

The equivalences `toLin_mem_order_iff` and
`toLin_mem_endFiltration_one_iff` compare `InOrd` with `𝔄(L)` and `InRad`
with `End^1(L)`. Applying these tests to a unit, its inverse, and its
difference from the identity gives the unit group identities
`stdToAut_mem_unitFiltration_zero_iff` and
`stdToAut_mem_unitFiltration_one_iff` for `J0` and `J1`.

In `layerReduction_entry`, the `i`-th component of a layer reduction
`φ` at `stdToAut x` for `x ∈ J0` is the residue of the `i`-th diagonal
block of `x`. Evaluate `IsLayerReduction` on the lifted basis vector
`liftVec (a', i)` and reduce its matrix image in `L_i / L_(i+1)`. The
later-block terms have vectors in `L_(i+1)`. The earlier-block terms have
coefficients in the maximal ideal, which again puts them in `L_(i+1)`.
The remaining terms are the diagonal block acting on the residue basis.
This identifies the quotient action appearing in BK93 (5.5.10)(b).
[Source details](LevelZeroNonmaximalTypeJacquetProof.md#source)
