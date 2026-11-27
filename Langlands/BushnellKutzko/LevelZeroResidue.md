# Residues of integral elements of a nonarchimedean local field

`res x` extends the residue map `IsLocalRing.residue` of `𝒪[F]` to `F` by
zero outside `𝒪[F]`. For integral arguments, it preserves addition,
multiplication, negation, subtraction and finite sums. In this range,
`res_eq_zero_iff` identifies its kernel with the maximal ideal, and
`res_eq_res_iff` characterizes equality of residues by the difference
lying in the maximal ideal. The operation `lift c` chooses an integral
representative of `c`, with integrality and reduction given by `lift_le_one`
and `res_lift`. These are direct consequences of the valuation and residue
map of the valuation ring.
