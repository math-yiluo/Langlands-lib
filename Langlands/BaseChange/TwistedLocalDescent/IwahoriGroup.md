# The Iwahori factorization of Haar measure on a congruence subgroup

Module `Langlands.BaseChange.TwistedLocalDescent.IwahoriGroup`.

Let `𝕂` be an ultrametric, proper, nontrivially normed field.

`restrict_congruenceBall_eq_map_mul_lowerUnit`: let `μG` be a Haar measure on `GL_n(𝕂)`, `μP` a
left Haar measure on the standard parabolic `P`, `νS`, `νL` additive Haar measures on `𝔭` and `𝔲̄`,
and `U` a compact congruence subgroup of radius `0 < r < 1`. Then

`μG|_U = c · ((μP|_{P ∩ U}) × νL|_{B(0,r)}).map ((p, Z) ↦ p (1 + Z))`

with `c = iwahoriConstant B μG μP νS νL U r = a / b`, where
`a = μG(U) ν(B(1,r))⁻¹` (`ν = blockSumMeasure B νS νL`) and `b = μP(P ∩ U) νS(R)⁻¹` are the
constants of `map_val_restrict_congruenceBall` and `map_val_restrict_parabolic_congruenceBall`.

Proof: `g ↦ g` is a measurable embedding of `GL_n` into `M_n`, so it suffices to compare the
images. The left side maps to `a • ν|_{B(1,r)}`; the right side maps to
`c · b · (νS|_R × νL|_{B(0,r)}).map ((X, Z) ↦ X (1 + Z))`, which is `a • ν|_{B(1,r)}` by
`map_mul_one_add_restrict`. The constant `b` is finite and nonzero (`P ∩ U` and `R` are compact
open).
