# Rank normal form with the identity in the first coordinates

`erMat R r` is the diagonal `f × f` matrix with `1` in the first `r`
positions and `0` elsewhere. By `exists_erMat_form`, a nonzero singular
square matrix `X` over a field can be written as `P * erMat k r * Q` with
`P, Q` invertible and `0 < r < f`. The proof uses Mathlib's rank normal
form. The identity `map_erMat` shows that ring homomorphisms preserve this
matrix, allowing the normal form over the residue field to be compared
with an integral matrix. [Transposition step](LevelZeroSwapStep.md)
