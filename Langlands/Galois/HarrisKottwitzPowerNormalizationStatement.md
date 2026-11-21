# Arithmetic normalization of the Kottwitz power family

`Langlands.GaloisRepresentation.HarrisKottwitzPowerNormalizationStatement`
is the last scalar-normalization step after concentration and the
Kottwitz comparison. It takes a fixed spectral system of the source class,
a number field `L` with realization `ι`, one integer `a ≠ 0`, and a single
collection `M` of actual representations over all `L_λ`. The input polynomials
`Q_v` are monic of degree `r+1`, have nonzero constant term, and are pure of
weight `r+w` at good places. The Euler polynomial of `M_λ` there is the
reverse of `Q_v ^ a.natAbs` after applying `L → L_λ`, for coefficient residue
characteristic different from that of `v`.

The scalar removed from `M_λ` is the inverse of a supplied actual continuous
Hecke avatar `ψ_λ`. The algebraic Hecke character and its common finite-part
values `β_v ∈ Lˣ` satisfy `IsUniformHeckeAvatar` in the Library's **geometric
Frobenius** convention. All conjugates of `β_v` have weight `w`, which need
not be zero. The input at the chosen complex realization compares the
reverse of `Q_v` to `clozelEulerPolynomial` with variable multiplied by
`ι(β_v)`. Twisting the original action by `ψ_λ⁻¹`, not inverting a Galois
action, gives `HarrisPowerSystem` on the same carrier family with multiplicity
`a.natAbs > 0` and with the output purity weight `r = (r+1)-1`.

`MonicCharacteristicPowerRootDescentStatement` isolates the elementary
rationality input when initially only the power is known over the common
field: a monic root of a positive power over a larger field has coefficients
in the original field, and the descended monic polynomial is unique. The
intended proof recovers successive coefficients from the leading end of the
power by division by its exponent. If the Kottwitz degree factor is already
supplied over the common field this step is unnecessary.

## Provenance and limits

This is derived from Clozel 1991, §5.2, equations (5.11)–(5.12), (5.31) and
the power identity on p. 142, with the change in scalar weight in §5.3,
pp. 143–144, and Kottwitz 1992, Theorem 1, p. 657 and §5 purity, p. 661.
The desired arithmetic `GL(n)` normalization is already expressed by
`clozelEulerPolynomial`; this interface does not identify a geometric
Frobenius lift with its inverse. The proof must compare `det(1-TFrob)` using
`eulerPolynomial_twist` and actual unramifiedness, preserve the positive
power, and subtract the scalar eigenvalue weight. It does not construct
`Q`, derive the scalar formula, prove occurrence/concentration, or extend
coefficients of any PEL cohomology. Those are upstream interfaces on the
same family: over the chosen common field, `M` must be the scalar extension
of the selected `cmHarrisLambdaHeckeMultiplicityObjects`, not a new unrelated
family. Only propositions and the canonical twist operation are defined here.
