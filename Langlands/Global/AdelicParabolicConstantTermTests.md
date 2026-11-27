# Constant terms and Levi tests of moderate-growth functions on parabolic quotients

Module `Langlands.Global.AdelicParabolicConstantTermTests` studies the constant term
`C_J f(g) = ∫_{U_J(F) \ U_J(𝔸)} f(u g) du` (`StandardParabolicFamily.constantTerm`) of a
function `f` on `U_Q(𝔸) M_Q(F) \ G(𝔸)`, for standard indices `J ≤ Q` of a standard parabolic
family. The function `f` need not be automorphic. The hypotheses are only:

- left invariance under `U_Q(𝔸) M_Q(F)` (`parabolicQuotientSubgroup` of `P_Q`);
- continuity;
- moderate growth for a closed matrix embedding `rho` (`HasModerateGrowthFunction`), where needed.

Intertwining integrals at regular parameters are of this kind (module
`Langlands.Global.AdelicStandardIntertwiningRegularity`). Their automorphy in the full sense
(finiteness under `K_∞` and under the center of the enveloping algebra) is not needed for the
results below.

## Results

- `rationalLeviImage_le_of_le`: for `J ≤ Q`, the rational points of `M_J` lie in
  `U_Q(𝔸) M_Q(F)`. The group lies in `P_Q`, whose rational points lie in `U_Q(𝔸) M_Q(F)`
  (`rationalImage_le_parabolicQuotientSubgroup`). The same holds for the radical `U_J`
  (`rationalRadicalImage_le_of_le` of `Langlands.Global.AdelicConstantTermAutomorphyProof`).
- `radicalIntegrand`, `radicalIntegrand_mk`, `constantTerm_eq_integral_radicalIntegrand`: the
  integrand `u ↦ f(u g)` descends to the compact quotient `U_J(F) \ U_J(𝔸)`, and the constant
  term is its integral for the normalized quotient measure.
- `continuous_constantTerm_of_le`: `C_J f` is continuous when `f` is. The descended integrand is
  jointly continuous on `G(𝔸) × U_J(F) \ U_J(𝔸)`, and the quotient is compact
  (`continuousOn_integral_of_compact_support`).
- `constantTerm_leviRational_mul_of_le`: `C_J f(m g) = C_J f(g)` for every rational point `m` of
  `M_J`. Conjugation by `m` is an automorphism of `U_J(𝔸)` preserving `U_J(F)`. It preserves the
  normalized probability measure of the quotient
  (`AdelicSubgroupPoints.measurePreserving_rationalQuotientAutomorphism`), and
  `f(u m g) = f(m (m⁻¹ u m) g) = f((m⁻¹ u m) g)` by the invariance of `f` under `m`.
- `hasModerateGrowth_constantTerm_of_le`: if `‖f(g)‖ ≤ C ‖g‖^r`, then `C_J f` satisfies a bound
  of the same form, with the same exponent `r`. Every class of `U_J(F) \ U_J(𝔸)` has a
  representative in a fixed compact set. The adelic source norm satisfies
  `‖u g‖^r ≤ H(u)^{|r|} ‖g‖^r` for the adelic height `H`, and `H` is bounded on the compact set.
- `constantTerm_mem_leviPairingDomain_of_le`: for a continuous, rationally invariant test `ψ` on
  `M_J(𝔸)` with integrable weighted majorants at every exponent (`HasLeviPairingMajorant`), the
  norm-one Levi pairing of `C_J f` with `ψ` converges absolutely at every `g`. This combines the
  three previous results with `mem_leviPairingDomain_of_moderateGrowth` (module
  `Langlands.Global.AdelicLeviPairingAutomorphicTests`).
- `constantTerm_finset_sum_of_le`: `C_J` is linear on finite combinations of continuous
  functions invariant under `U_Q(𝔸) M_Q(F)`, since each integrand is integrable
  (`integrable_constantTermIntegrand_of_le`).

## Sources

The constant term along a standard parabolic and the cuspidal tests (6.8) are those of J.
Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math.
Soc. 37 (2024), §6.2, p. 202, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. Moderate growth on
`U(𝔸) M(F) \ G(𝔸)` is the notion of C. Mœglin and J.-L. Waldspurger, *Spectral decomposition
and Eisenstein series* (1995), I.2.3, p. 25 (chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`), registered as
`moeglin-waldspurger-1995-spectral-decomposition`.
The proofs here follow the Library's corresponding results for functions on `G(F) \ G(𝔸)`
(modules `Langlands.Global.AdelicLeviConstantTermPairing` and
`Langlands.Global.AdelicConstantTermEvaluation`), with invariance under `U_Q(𝔸) M_Q(F)` in place
of invariance under `G(F)`.
