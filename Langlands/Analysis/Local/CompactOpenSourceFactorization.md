# Literal factorization with the common compact-open source scale

This derived unit implements the common scale fixed in J.-L. Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d’après Harish-Chandra)*
(2003), I.1, printed p.240 / PDF page 6 (zero-based index 5),
DOI 10.1017/S1474748003000082. The source fixes one special maximal compact
subgroup and gives each closed algebraic subgroup Haar measure of mass one
on its intersection with that compact. The generic Lean result takes the
compact open and closed subgroup carriers as supplied data. It does not
construct a special maximal compact or assert its reductive properties.

For a compact open `S` in `G`, the ambient measure is the existing
`normalizedCompactOpenHaar S hS`. Each closed subgroup receives
`subgroupCompactOpenHaar S hS`, the intrinsic regular Haar measure constructed
on its own carrier. All normalizations use the same original ambient elements.
No ambient Haar measure is restricted to a possibly null subgroup.

`sourceCompactOpenQuotientMeasure` selects an actual measure from the proved
`compatibleMeasureExists` theorem for these two exact Haar measures. The
selection requires a locally compact Hausdorff ambient topological group,
Borel structures and right invariance of both prescribed Haar measures.
`sourceCompactOpenQuotientMeasure_isCompatible` supplies the complete complex
Weil formula, integrability on compact continuous tests, regularity, nonzero
mass and right invariance under the actual quotient action. The module also
exports its regularity instance and nonzero lemma. Later integral witnesses
can be stated for this actual chosen measure; the definition does not replace
a measure already appearing in an integral witness.

For a second closed subgroup `K`, its compact open `B` is the inverse image
of `S`. The three masses in `compactOpenFactorScalar` are all exactly one.
The proof of `compactOpenFactorScalar_source` substitutes these three proved
mass identities into the finite nonnegative real quotient. Consequently
`compactOpenFactorMeasure_source` identifies the explicitly corrected factor
with the subgroup's original intrinsic source measure.

Suppose `m : H × K ≃ₜ G` is a supplied literal ordered multiplication chart,
`m(h,k) = h*k`, and the image of `(H intersect S) × (K intersect S)` under
that chart is exactly `S`. For any supplied quotient measure `ν` compatible
with the same ambient and subgroup source measures,
`IsCompatible.measurePreserving_sourceCompactOpenFactor` proves that the
actual complement-to-quotient chart preserves the source measure on `K`.
It applies the published local-product comparison and the preceding
identity for the factor measure. `ν` remains the same measure throughout.

With explicit ambient second countability,
`IsCompatible.measurePreserving_sourceCompactOpenProduct` derives the full
product normalization of `m` for the source Haar measures on `H`, `K` and
`G`. The proof transfers local compactness from closedness, inherits second
countability on the actual subgroup carriers, and uses the pinned Mathlib
instances for S-finiteness, product Borel structure and regularity of these
locally finite product measures. The existing compact-test/Fubini/Weil
product comparison then applies. No product measure identity is assumed.
The ordered multiplication chart is a homeomorphism; it is not asserted to
be a direct-product group isomorphism.

Right invariance is a visible additional premise, never inferred from
closedness alone. It can be supplied by the previously published
compact-open-cover unimodularity theorem, when the actual carrier has such
a cover. The literal global charts and local source-compact product geometry
remain genuine application obligations. This module proves neither their
general reductive realization nor arbitrary standard-intertwining
convergence, rational continuation or a whole-task Plancherel condition.
