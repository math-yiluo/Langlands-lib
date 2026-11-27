# Integral matrix lifts from the residue field

`liftO c` chooses an element of `𝒪[F]` with residue `c`, and `liftM X` uses
these choices entrywise to lift a matrix over `𝓀[F]`. For invertible `X`,
the lift has unit determinant over `𝒪[F]` since its reduction is
invertible. The resulting `liftGL X` has integral entries and integral
inverse by `isIntGL_liftGL` and reduces to `X` by `res_liftGL`.

The same determinant argument gives `exists_isIntGL_of_sub_one`. A matrix
congruent to the identity modulo the maximal ideal is invertible with
integral inverse. These lift properties are used in the finite residue
calculations for compression. [Transposition step](LevelZeroSwapStep.md)
