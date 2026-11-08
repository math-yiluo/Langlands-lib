# Shell identities for the twisted smeared test vector

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement` (Jacquet–Shalika 1985,
§4.4, printed pages 329–330, from (14) with (15)–(18) to the shell form of (13); here the
internal Kirillov shell vector replaces their `W'` of (16)–(17)). The canonical
structures are local instances, `abv` is the published `normalizedAbsoluteValue`, and the
quotient measure is the published `unipotentQuotientHaar`.

- `corankOne_integrable_of_whittakerType`: for `Π` on `GL_(m+2)` and `τ` on `GL_(m+1)` of
  Whittaker type, for the standard and the inverse character respectively, with nonzero
  functionals, the published corank-one integrand of two model vectors is integrable on a
  right half-plane. This is the first clause of the published `unequalRankAnalytic` (JPSS
  1983, Theorem 2.7) at the block `j = k = 0`, transported by
  `UnequalRankZeroRowAssembly.zero_row_converges_iff` and `unequalRankIntegrand_zero_zero`.
- `dualShellConstant_eq_mul`: if `ord ϖ = 1`, then
  `dualShellConstant(s) = dualShellConstant(0) · (q^(-s))^(-c(m+1))`. The only `s`-dependence
  is `|det(ϖ^(-c) I)|^(s-1/2)`, and `ord det(ϖ^(-c) I) = -c(m+1)`.
- `shell_identity`: hypotheses:
  - the data of `dual_shell_integral` (conductor `O`, `f ≥ 1`, `ω` trivial on `1 + 𝔭^f`,
    `ϖ^c O ⊆ 𝔭^f`, representatives `T` of the weight (4.4.18));
  - the Kirillov shell conditions on `f'`;
  - `Fbig` a model vector of `Π` equal to `twistedSmear …` and right invariant under an open
    subgroup;
  - `W''` a model vector of `τ`, right invariant under an open subgroup, with
    `W''(g ϖ^c) = ωτ W''(g)`;
  - a certificate `IsPadicPairGammaFactor F ψ ν Π τ G` with `G = C X^(c(m+1))`.

  Conclusion: there is a minus-one scalar `ζ` of the model of `τ` such that, for every `j`,
  the integral over `determinantSlice … m j` of the corank-one integrand at `s = 0` is
  `(ζ^(m+1))⁻¹ C⁻¹ c_d q^(c(m+1))` if `j = 0` and `0` otherwise. Here
  `c_d = dualShellConstant(0) ω(-1)⁻¹ ∫_(K⁰(f)) ω(k₀₀) W''(k) dk`.
  Proof: `dual_shell_integral` and `dualShellConstant_eq_mul` give the dual integral
  `c_d (q^(-s))^(-c(m+1))`. Then `corankOne_eq_const_of_gamma_monomial` gives a constant forward
  integral, `corankOne_integrable_of_whittakerType` gives absolute convergence, and
  `corankOne_shell_eq_of_const` extracts the shell coefficients.
