# Coefficients of the projected right-translation representation

In the proof of Theorem VIII.4.2, Waldspurger (2003), printed pp.330–331
(PDF pp.96–97), fixes a compact open `H` and lets `G` act by right
translations on `V = p_χ(°C(H \ G))`. He shows this representation is
admissible and unitary, hence semisimple, and that its coefficient space
consists of square-integrable functions modulo the centre. This module
proves one step of that argument for the actual projected representation
of `SchwartzProjectedRepresentation`: every matrix coefficient of the
representation is itself a central integral of a function in the ambient
translation-stable Schwartz subspace. Square-integrability of coefficients
then follows from square-integrability of the raw central images, which is
a separate input not treated here. The argument is an alternative to the
source's convolution identity. It uses Waldspurger's Lemma I.6.1,
printed p.249 (PDF p.15), and the `G × G`-equivariance of `p_χ`.

## Setting

`Γ` is a topological group with a compact open subgroup, `Ξ, σ` are
weights with `TranslationWeights`, `E` is a Schwartz subspace stable under
all two-sided translations (`IsTranslationStable`), `A` is a central
subgroup with any measure `muA` and any character `χ`, and `H` is any
subgroup. The representation is the published
`projectedLeftSubrepresentation ht E hE hA muA χ H`: right translation on
the span of the raw central images of the `H`-left-invariant part of `E`.

## Results

- `translate_mem_schwartzCentralIntegralImage`: a two-sided translate of a
  raw central integral `p_χ φ`, `φ ∈ E`, is `p_χ` of the translated
  Schwartz function, which lies in `E` by stability. The proof combines
  `Space.coe_translate` with `centralProjection_translate` from
  `SchwartzCompactLifting`. No convergence is needed.
- `twoSidedTranslateSpan_le_schwartzCentralIntegralSpan`: hence the span
  `V_{ρ×λ}(f)` of all two-sided translates of such an `f` lies in the span
  of the raw image of `E`.

The remaining results assume `hc : CentralIntegralConvergesOn E muA χ`.

- `projectedLeftSubrepresentation_mem_ambient_image`: every vector of the
  projected representation is a raw central integral of an element of `E`.
  This is `projectedLeftSubrepresentation_mem_image` of
  `SchwartzProjectedRepresentation` followed by
  monotonicity of raw images along `schwartzLeftLevel E H ≤ E`.
- `isRightAdmissible_of_mem_projectedLeftSubrepresentation`: if the
  projected representation is admissible, every vector `v` lies in
  Waldspurger's `A_ρ` (`IsRightAdmissible`). Its Schwartz preimage is
  bi-invariant under some compact open `J`, so `v` is `J`-bi-invariant
  (published `IsBiInvariant.centralProjection`). The right-translate span
  `V_ρ(v)` is a subrepresentation of the projected representation
  (`FiniteVectors.orbitSpan_le`). It is therefore admissible by
  `isAdmissible_of_injective` along `inclusionOfLe`.
- `coefficientFunctionSpace_projectedLeftSubrepresentation_le`: if the
  projected representation is admissible, the coefficient space of the
  smooth representation `SmoothRep.of R ha.1`, where
  `R = (projectedLeftSubrepresentation ht E hE hA muA χ H).toRepresentation`,
  lies in `schwartzCentralIntegralSpan E muA χ`. For a smooth functional
  `ℓ` and a vector `v`, the functional `ℓ` restricted along the inclusion
  `V_ρ(v) → V` is smooth (`isSmoothVector_map` for `dualIntertwining`). By
  `matrixCoefficient_intertwining` the coefficient `g ↦ ℓ(R(g) v)` is a
  coefficient of the right-translation representation `rightTranslateRep`
  on `V_ρ(v)`. By the published Lemma I.6.1,
  `twoSidedTranslateSpan_eq_coefficientFunctionSpace`, it lies in
  `V_{ρ×λ}(v)`, which lies in the span of the raw image by the previous
  results.
- `coefficientFunctionSpace_projectedLeftSubrepresentation_subset_image`:
  under the same hypotheses each coefficient is a single raw central
  integral, because convergence identifies the span with the raw image
  (`coe_schwartzCentralIntegralSpan_eq_image`).

## Recorded proposition

`ProjectedCoefficientClosureStatement.{uG}` quantifies the setting above
over all groups `Γ : Type uG` and states the inclusion of
`coefficientFunctionSpace_projectedLeftSubrepresentation_le`.
`projectedCoefficientClosure` proves it by that theorem. The proposition
is an internal interface for the reverse inclusion of Theorem VIII.4.2. It
records a proved result and adds no hypothesis to any target.
Admissibility of the projected representation (from VIII.4.1, see
`isAdmissible_projectedLeftSubrepresentation`) and convergence remain
explicit hypotheses supplied by their own proofs.
