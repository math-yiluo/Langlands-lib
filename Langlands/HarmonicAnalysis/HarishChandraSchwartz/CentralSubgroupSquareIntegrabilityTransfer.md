# Transferring square integrability between central quotients

This module is internal measure and representation glue. It combines the
published arbitrary-central-subgroup pushforward results of
`Representation.Unitary.CentralSubgroupForm` with
`Plancherel.centralSubgroupCoefficientLpComparison`, then specializes their
hypotheses on actual rational points. It makes no new original-literature
assertion.

The generic declarations are in `Langlands.Plancherel`. Let `G` be a
topological group, `C` a normal central subgroup and `muC` the displayed
measure on `G/C`. `centralSubgroupFullQuotientMeasure C hC muC` is exactly
its pushforward along the actual quotient homomorphism `G/C -> G/Z(G)`.
The definition changes no scalar normalization and selects no independent
measure on the full central quotient.

For a locally compact second-countable group, Borel-compatible quotient
measurable spaces, compact-open cofinality and an irreducible representation
square integrable modulo `C`,
`centralSubgroupFullQuotientMeasure_isHaar` proves that this actual pushforward
is Haar. The proof uses admissibility and compact-open duality to choose a
nonzero smooth functional and a vector on which it is nonzero, then applies
the published pushforward-Haar theorem. That theorem uses the L2 coefficient
to establish local finiteness on the full central quotient.
The original `C` is not required to be closed.

`isSquareIntegrableModCenter_fullQuotientMeasure` retains the original
admissibility and unitary central-character witness and pushes forward the
L2 property of every smooth-dual coefficient with
`centralSubgroupCoefficientNorm_memLp_map`. Its statement installs the proved
Haar instance on this exact pushforward measure.

`isSquareIntegrableModCentralSubgroup_transfer` additionally takes a closed
normal central subgroup `A`, compactness of `Z(G)/(A in Z(G))`, a Borel
measurable structure on `G/A`, and any displayed Haar measure `muA` on it.
For a Hausdorff locally compact second-countable ambient group, it transfers
square integrability from the original `C,muC` to `A,muA` by passing through
the actual pushed-forward full-center measure and applying the published
compact-central-fiber coefficient Lp comparison. No containment relation
between `C` and `A` is assumed. There is no valuation-index hypothesis.
The generic group and representation-carrier universes are independent.

The actual-point theorem is in `Langlands.HarishChandraSchwartz`:
`isSquareIntegrable_splitComponent_of_centralSubgroup`. Its data are a
connected reductive group over any nonarchimedean local field, an actual
split component `s`, the original irreducible admissible representation of
`G(F)`, an arbitrary normal central point subgroup `C`, and its displayed
quotient Haar measure with square integrability. Both the original quotient
and the actual split-component quotient have explicit Borel compatibility.
For every Haar measure on the latter quotient, the theorem concludes square
integrability of the same representation modulo the actual point image of
`s`.

The implementation derives compact-open cofinality from the canonical
rational-point topology, derives closedness of the actual split-component
image, and uses the published
`compactSpace_center_quotient_splitComponent` to supply compactness of the
full abstract center modulo that image. It installs the canonical Borel
structure on the auxiliary full-center quotient and applies the generic
transfer. The field and representation-carrier universes remain independent;
no splitness or quasisplitness of the ambient group and no characteristic
restriction is introduced.

This unit supplies the arbitrary-central-subgroup to actual split-center
square-integrability bridge. It does not prove a coefficient Xi bound,
uniform exponent or threshold result, positive-part decay, or full wave-packet
Schwartz membership. The Borel premises are essential to applying the
measure-transport results; the module does not infer them from an arbitrary
measurable-space structure or change the original packet targets.
