# From shell identities to the averaged function: the completeness step

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. Jacquet–Shalika 1985,
§4.4, printed page 329, deduce from the identity (13), valid for all test representations
of the smaller group, that the averaged function equals a multiple of the target. They use
Corollary (3.3) (printed pages 325–326), which rests on the completeness lemma, Lemma (3.2),
printed page 325. In the Library that lemma is the published
proposition `Whittaker.WhittakerCompletenessStatement`, taken here as the hypothesis `hT1`. This
module carries out that deduction shell by shell.

## Algebra

- `firstColumnWeight_principal_mul`: the weight `ω(k₀₀)⁻¹ 1_(K⁰(f))` is left invariant under
  the principal congruence subgroup of level `f` (`ω` trivial on `1 + 𝔭^f`).
- `model_rightInvariant`: a coefficient-model vector of a smooth representation is right
  invariant under an open subgroup (published `model_isSmooth`).

## Canonical p-adic setting

- `standardCharacter_eq_one_of_integral`: if `ψ` has conductor `O`, the published standard
  character is trivial on integral unipotents.
- `ord_det_mul_integral`: `ord det(g k) = ord det g` for `k ∈ GL_(m+1)(O)`, from the published
  `normalizedAbs_det_of_mem_integralSubgroup`.
- Properties of the weighted right average `rightAverage` (DualAverage) with the weight of
  `K⁰(f)`: `rightAverage_firstColumn_unipotent` (left `(N, ψ_N)`-equivariance),
  `rightAverage_firstColumn_principal` (right invariance under the principal congruence
  subgroup, by left invariance of the Haar measure and of the weight), and
  `rightAverage_firstColumn_support` (a nonzero average at `g` forces `F_A(g k) ≠ 0` for some
  `k ∈ K⁰(f)`).
- `shellRestriction F F_A j = F_A · 1_(ord det = j)`, with `shellRestriction_mul_integral` and
  `shellRestriction_unipotent`. `rightAverage_shellRestriction`: averaging commutes with the
  restriction to a shell. `rightAverage_shell_support`: the averaged shell function is supported
  in `N C K⁰(f)` when `F_A` on the shell is supported in `N C`.
- `rightAverage_eq_target_of_shells`: hypotheses:
  - `F_A` is right invariant under an open subgroup, with `F_A(u g) = ψ_N(u) F_A(g)` for the
    published `standardCharacter ψ m`;
  - on every shell `F_A` is supported in `N C` for a compact `C`;
  - for every representation `π` generic for `ψ⁻¹ = ψ.scale (-1)`, every functional `ℓ`,
    every model vector `w` (right invariant under `L_w`) and every `j`,
    `∫ (F_A · 1_(ord det = j)) w_avg = [j = 0] c ∫ t w`. Here `w_avg` is the inverse
    `K⁰(f)`-average of `w` and `t` is the target `firstColumnTarget ω hf (standardCharacter ψ m)`.

  Conclusion: the weighted `K⁰(f)`-average of `F_A` equals `c t`.
  Proof: for each `j`, `H_j = average(F_A · 1_j) − [j = 0] c t` is an inverse Whittaker
  function for `ψ⁻¹` (`inverseStandardCharacter_scale_neg_one`). It is right invariant under
  the principal congruence subgroup and supported in `N (C K⁰(f) ∪ K⁰(f))`. For every `π`,
  `ℓ` and `w`, the integral of the published `whittakerProductIntegrand` of `w` and `H_j` is
  `∫ w · average(F_A 1_j) − [j = 0] c ∫ w t`. The adjointness `integral_rightAverage_pair` and
  the hypothesis show that this is `0`, with integrability from
  `integrable_out_of_compact_support`. So `hT1` gives `H_j = 0`. At `g` take `j = ord det g`.
  The target vanishes off `ord det = 0`, since `N K⁰(f) ⊆ {ord det = 0}`.
