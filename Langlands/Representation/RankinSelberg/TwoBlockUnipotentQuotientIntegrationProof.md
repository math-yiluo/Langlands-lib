# Normalized integration for the two-block unipotent quotient

Module `Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationProof`.
Authors: Worker 113 and Worker 235.

The theorem `Langlands.RankinSelberg.twoBlockUnipotentQuotientIntegration.{uF}`
proves the unchanged Library proposition
`Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement.{uF}`.
It is closed: the canonical p-adic field, two positive block ranks, rank equality,
and arbitrary rectangular additive Haar measure are universally quantified by
that proposition. The ambient and subgroup measures, actual left quotients,
projection, radical fibers, and product measurable structures are exactly those
in the statement.

This is derived analytic infrastructure for the transition in JPSS (1983),
Section 4.6, from equation (4) on printed page 411 to the first integral on page
412, using the block subgroup in display (5). The kernel and arbitrary-Haar
normalization are the Library statement's representation-free formulation of
that transition. The proof below follows the implemented measure and kernel
argument, rather than attributing this closed proposition verbatim to JPSS.

The implementation assembles four pieces of internal support.

1. **Fixed measures and existence.** `TwoBlockUnipotentMeasures` defines
   `blockHaar` as exactly the pushforward of the product of the two normalized
   unipotent Haar measures. Its Haar, regularity, and right-invariance instances
   transport these properties through the block group homeomorphism. The
   published full-unipotent right-invariance instance supplies the other
   subgroup witness. `fullUnipotent_compatibleMeasureExists` and
   `block_compatibleMeasureExists` apply the closed-subgroup compatible-measure
   existence theorem to the fixed ambient Haar. For the supplied rectangular
   measure `μR`, `integerCube_mass_pos_lt_top` proves that its integral cube is
   compact, open, and nonempty, so its mass `c` is positive and finite.

2. **The actual s-finite kernel.** `TwoBlockUnipotentFiberKernel` constructs
   `fiberKernel F h μR` by descending the family of pushforwards along
   `x ↦ [upperRadical(x) * g]_H`. Joint continuity gives measurability.
   The actual change of representative is an affine rectangular map whose
   linear part comes from unipotent blocks; determinant-one Haar transport
   and translation preserve the supplied `μR`. Consequently the family
   descends to the full-unipotent left quotient. `fiberKernel_mk` gives the
   prescribed equality of measures for every representative.
   `TwoBlockUnipotentFiberProper` proves that the radical fiber has compact
   preimages of compact sets, using a compact lift in the ambient group and
   the continuous radical coordinate. Haar compact finiteness makes every
   kernel fiber finite on compact sets. A common countable compact cover of
   the block quotient proves `IsSFiniteKernel` via `fiberKernel_isSFinite`.
   The final theorem chooses this one kernel before quantifying over compatible
   quotient measures.

3. **The normalized measure tower and restrictions.**
   `TwoBlockUnipotentQuotientCoordinates` constructs the homeomorphism
   `(b,x) ↦ b * upperRadical(x)` from `H × R` to `N` and proves
   `map_coordinates_prod`. Its normalization is determined on the integral
   points: `blockMeasure_integral` gives block mass one, the rectangular
   factor has mass `c`, and the full-unipotent Haar has integral mass one.
   The transported measure is therefore `c • μN`.
   In `TwoBlockUnipotentQuotientTower`, `comp_eq_smul` applies this transport
   to nonnegative continuous compactly supported ambient functions and uses
   the compatible real Weil formulas for both quotient measures. Positive
   lifting of compact quotient test functions first proves compact finiteness
   of the composed measure. Regularity and equality on compactly supported
   tests then prove `κ ∘ₘ νN = c • νH`.
   For any compatible `νN` and `νH`, their regularity implies finite mass on
   compact sets. Both quotients are locally compact and second countable,
   hence sigma compact; they therefore have sigma-finite measures. The final
   proof installs these instances directly from compatibility and the open
   quotient maps. `comp_restrict_eq_smul` uses
   `projection (fiberPoint x g) = [g]_N` to restrict the same tower to every
   measurable base set `s`, obtaining
   `κ ∘ₘ (νN.restrict s) = c • (νH.restrict (projection ⁻¹' s))`.

4. **Tonelli, absolute integrability, and the actual average.**
   `TwoBlockUnipotentQuotientAnalysis.analytic_of_comp_eq_smul` applies to
   each restricted identity. Kernel composition gives the nonnegative
   iterated integral. Since `0 < c < ∞`, integrability against `c • νHs`
   is equivalent to integrability against `νHs`; the kernel composition
   criterion gives exactly almost-everywhere fiber integrability together
   with integrability of the real fiber norm integral. The kernel's
   representative law identifies its complex fiber integral pointwise with
   the published `radicalAverage`. The Bochner composition theorem then
   proves both integrability of that average and its integral formula with
   scalar `c.toReal`.

Thus the factor remains the mass of the supplied rectangular Haar throughout,
with `c` on the specified side of the tower and Tonelli formulas. The proof
establishes the absolute-integrability criterion as well as the identities.
It makes no assertion about convergence of future representation-specific
integrands or the subsequent general-linear disintegration in display (6).

Worker 113 supplied the fixed measures, measurable-kernel and properness
support, and the final assembly. Worker 235 supplied the coordinates,
normalization, quotient tower, and analytic support. The theorem uses only
the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
