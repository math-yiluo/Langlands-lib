# Continuous Levi pairings of unipotent constant terms

Let `J` be a standard parabolic in `StandardParabolicFamily`. For a fixed ambient
adelic point `g` and a fixed continuous rational-invariant test `ψ` on its Levi,
`constantTermLeviPairingCLM` is the continuous complex-linear form

\[
  v \longmapsto \int_{M(F)\backslash M(\mathbb A)^1}
    (C_Jv)(\iota(m)g)\,\overline{\psi(m)}\,dm .
\]

The domain is the ambient uniform-growth stage, `C_J` is the normalized unipotent
constant term, and `ι` is the actual Levi map into the ambient group.
`constantTermLeviPairingCLM_apply` identifies this expression with `leviPairing` of
`constantTerm`, using the existing norm-one rational quotient and its Haar measure.

The pairing is the one used in Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, §6.2, (6.8), p. 202. The continuous linear construction here is
derived from the norm-one pairing and the order-zero growth estimate for constant
terms, as in §7.1 and `AdelicConstantTermEvaluation`. The test is assumed to satisfy
`HasLeviPairingMajorant`. This requires an integrable real function on the norm-one
quotient that bounds the absolute test value times the ambient growth weight at
some representative of almost every class.

The standard parabolic normalizes its radical. Naturality of the principal-point map
and invariance of normalized constant terms under rational normalizers therefore give
invariance under the principal Levi points. This proves that the value of the product
in the integrand is independent of the representative. Its pullback to the norm-one
Levi is continuous by continuity of the normalized constant term on the ambient
group and continuity of the test. It is thus continuous on the quotient.

The bound in `exists_leviPairing_constantTerm_bound` follows by evaluating the integrand
at the representatives from the majorant hypothesis. The pointwise constant-term
estimate bounds its absolute value by the majorant times a fixed constant and the
order-zero seminorm of `v`. This gives integrability of the integrand and a seminorm
bound for the integrated value. Linearity follows by integrating the pointwise
continuous linear evaluations. The seminorm bound gives continuity at zero and hence
continuity of the linear form.
