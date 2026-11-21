# Existence of an Iwasawa-compatible Haar measure on the Levi

`Langlands.Global.iwasawaCompatibleMeasureExistence` proves the published
`Langlands.Global.IwasawaCompatibleMeasureExistenceStatement`. For the
presented parabolic `P = MU` and compact factor `K` in the statement, it
supplies a Haar measure on `M(𝔸)` compatible with Mathlib's Haar measure on
`G(𝔸)`, normalized unipotent Haar measure and probability Haar measure on
`K`. This is the measure premise of the published reduction of Lapid's
Proposition 6; this file does not prove the other two premises.

The proof applies `iwasawaCompatibleMeasureIntegrationReduction` to
`AdelicGroupPoints.adelicIwasawaIntegration` and
`AdelicGroupPoints.adelicParabolicModulus`, both at universe zero. The first
theorem gives the Iwasawa integral with a positive scalar and the Mathlib
Haar measures on `M(𝔸)` and `U(𝔸)`. The second identifies the parabolic
modulus with the modular character; the reduction then identifies the
inverse modulus in the integral with the inverse adjoint-determinant norm
`m^{-2ρ_P}`. The reduction transports unipotent Haar measure to the
adelic image of `U`, where it is a positive multiple of the normalized
measure. It absorbs that multiplier and the Iwasawa scalar into Haar
measure on `M(𝔸)`. This gives the integral in the statement without an
extra constant.

The measure convention comes from C. Mœglin and J.-L. Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.1.13, printed
p. 18 (chapter PDF p. 18), registered as
`moeglin-waldspurger-1995-spectral-decomposition`. The published reduction
implements the normalization for the actual adelic groups in the pinned
statement, without a central cover.
