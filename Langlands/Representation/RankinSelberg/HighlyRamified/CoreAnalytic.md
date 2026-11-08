# Analytic glue for the adjacent-rank step

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. Small analytic and
equivariance facts used to assemble the Jacquet–Shalika 1985 §4.4 core (`core_gamma_eq`). The
source treats them as routine. The canonical topology, valuation and Borel structures of the
p-adic field are local instances.

- `hasIntegerConductorAt_of_additiveConductor_eq_zero`: an additive character of conductor
  exponent `0` satisfies `HasIntegerConductorAt` (FourierRow): it is trivial on `O`, and for
  non-integral `t` some integral `z` has `ψ(z t) ≠ 1`. Proof: the published conductor property
  (`hasIntegerConductor_of_additiveConductor_eq_zero`, EssentialInput), with the complex and
  circle values of `ψ` compared by `Circle.ext`.
- `determinantWeight_mul_integral`: `|det(g k)|^s = |det g|^s` for `k ∈ GL_(m+1)(O)`
  (published `normalizedAbs_det_of_mem_integralSubgroup`).
- `continuous_corankOneIntegrand`, `measurable_corankOneIntegrand`: if `W` and `W'` are right
  invariant under open subgroups, the corank-one integrand on `N \ GL_(m+1)` is continuous,
  hence measurable. The function on the group is right invariant under the intersection of
  the two subgroups (pulled back along `diag(·,1)`) and `GL_(m+1)(O)`. The published
  `LastRowReduction.continuous_of_rightInvariant` and `continuous_descend` apply.
- `corankRestriction_mul`, `corankRestriction_unipotent`: the restriction
  `F_A(g) = U(diag(g,1)) |det g|^(-1/2)` (`corankRestriction`, ShellDischarge) is right invariant
  under that intersection, and `F_A(u g) = ψ_N(u) F_A(g)` (published
  `corankOne_standardCharacter`).
- `corankRestriction_shell_compact`: for each `j`, some compact `C` satisfies
  `ord det g = j`, `F_A(g) ≠ 0` ⇒ `u g ∈ C` for some `u ∈ N`. This is the hypothesis `hFAsupp` of
  `rightAverage_eq_target_of_shells`. The proof follows the published
  `CommonLevel.corank_common_compact_support`, with the compact set taken in the group:
  `g = u · diag(a) · κ` with `κ ∈ GL_(m+1)(O)` (`exists_unipotent_diagonal_integral`). The
  published `root_bound` and `corank_diagonal_upper` bound every `|a_i|` above by `M`. The fixed
  `|det g| = q^(-j)` bounds them below by `q^(-j) / M^m`. `C` is the image of the product of
  these annuli with `GL_(m+1)(O)`.
- `dualWeightFourier_hasCompactSupport`, `dualWeightFourier_isLocallyConstant`: the weight
  `S₂(rev x)` of DualShell is supported in `O^(m+1)` and locally constant. On the clopen set
  `O^(m+1)` each character term is locally constant because `ψ` is trivial on `O`
  (`eventually_character_eq`). Off that set the weight is `0`. These are the hypotheses of
  `exists_twistedSmear_model` (TwistedSmearModel).
- `whittaker_dualConj_unipotent`: `Ξ(A) = W(M(diag(A,1)))` satisfies
  `Ξ(u A) = ψ_N(u)⁻¹ Ξ(A)`. `M(diag(u,1))` is the published reflected unipotent of
  `diag(u,1,1)`, and `standardCharacter_reflected` and `corankOne_standardCharacter` compute its
  character.
