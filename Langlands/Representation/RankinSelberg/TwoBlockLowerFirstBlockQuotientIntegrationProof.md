# Linked lower mixed quotient integration: proof

Module
`Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationProof`.
Authors: Worker 1196 and Worker 1179.

The theorem
`Langlands.RankinSelberg.twoBlockLowerFirstBlockQuotientIntegration`
has complete type
`Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotientIntegrationStatement.{uF}`.
It proves the unchanged closed proposition for every canonical p-adic field
in arbitrary field universe, every positive two-block shape, every integer
determinant slice and every supplied rectangular additive Haar measure.

The source is Jacquet–Piatetski-Shapiro–Shalika (1983), *Rankin-Selberg
convolutions*, Section 4.9, equations (2) and (8), printed pages 416 and 418,
with the block groups on printed pages 412–413. The registered source is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The shared normalization, compatible quotient measures, kernel identities
on each slice, Tonelli laws and absolute-integrability criteria are derived
precision for those source formulas.

## Fixed measures and existence

Write `a = m 0 + 1`, `b = m 1 + 1`, `G = GL_{t+1}(F)`, and
`q = F.canonicalTopologicalData.residueCardinality`. All topology, valuation,
local-field and Borel structures are the canonical ones from the target.
The actual rectangle and the binary coordinate products retain their
product measurable structures.

`assembleLowerFirstBlockQuotientIntegration` selects `normOneHaar F (m 0)`
on `GL_a^0`, whose subtype pushforward is the restriction of the specified
`generalLinearHaar F.Carrier (m 0)`. The mixed Haar is the pushforward of
its product with the specified `N_b` Haar. It selects the single fixed
`lowerMixedHaar F h` on `L⁻`, normalized to give its integral points
mass one, before quantifying over supplied rectangular Haar measures.

The lower-unipotent Haar is exactly the pushforward of the specified full
unipotent Haar under the inverse of `conjugationEquiv h F.Carrier`.
`measurePackage F h` supplies compatible measure existence for all four
quotients and sigma-finiteness for every compatible choice. It also proves
compatibility and sigma-finiteness of the lower quotient measure obtained
from the standard full-unipotent quotient by the inverse of
`lowerToStandard h F.Carrier`. This quotient map acts by left
multiplication by the rotation matrix. The subgroup map used for the Haar
measure acts by conjugation. The proof retains these distinct maps with
their prescribed inverses.

Haar, regularity and right-invariance certificates come from the measure,
normalization and transport support modules. The actual projections to the
lower mixed quotient are measurable by continuity, and their determinant
slice preimage identities hold for every integer.

## Rectangular tower: equation (2)

For any supplied rectangular additive Haar `μR`, put
`c = μR {Z | ∀ i j, Z i j ∈ O}`. The integral cube is compact and has
nonempty interior, giving `0 < c < ∞`. The normalization theorem gives

```text
map lowerMixedSubgroupHomeomorph
  (μR.prod (normOneHaar.prod μNb)) = c • lowerMixedHaar.
```

The common lower mixed Haar remains fixed as `μR` varies.
`radicalIntegration F h μR νL hL νM hM` supplies the actual measurable
s-finite rectangular kernel, its equality of measures at every
representative, and the restricted identity

```text
κR ∘ₘ νL.restrict LQ0 = c • νM.restrict MQ0.
```

The supporting radical tower first establishes the full quotient identity
by quotient integration and equality of regular measures, then restricts
it using the exact preservation of determinant slices along radical
fibers. Its specialization here uses the zero slice on both quotients.
The analytic support identifies the published `radicalAverage` with the
kernel integral and derives the full Tonelli law, the fiberwise
absolute-integrability equivalence, and the conditional outer strong
measurability, integrability and Bochner identity. The coefficient `c`
appears on the mixed-quotient side as required.

## First-block tower: equation (8)

`lowerFirstBlockSliceTowerInput` applies
`firstBlockKernel_comp_zeroSlice` to the exact compatible measures.
For every integer `k`, it proves

```text
d_k • (firstBlockKernel F h νA hInvariant k ∘ₘ νL.restrict LQ0)
  = νMinus.restrict HQk,
d_k = ENNReal.ofReal (q ^ (-(k * b))).
```

The geometric theorem uses the actual first-block fibers
`[v], [g] ↦ [diag(v,1) g]`. Its proof writes the prescribed lower-unipotent
Haar in block coordinates and uses
`diag(x,y) R(Z) diag(v,1) = diag(x v,y) R(Z v)`.
The rectangular Haar change of variables under `Z ↦ Z v` is compensated
by `q^(-k b)`. The small quotient orbit kernel on slice `k` unfolds to
the left translate `z GL_a^0`, where `ord(det z) = k`. This yields the
lower mixed average of the left-translated test function. The common
positive finite cube mass cancels.

Integrating this equality on `LQ0`, compatibility and left invariance of
the ambient Haar give the ambient slice-`k` test integral. Compatibility
of the lower quotient gives the same value on `HQk`. Positive compactly
supported quotient lifting and uniqueness of regular measures extend
equality from these test functions to the displayed measure identity.
Thus the outer slice stays zero for every `k`; the lower quotient slice is
`k`, and the identity contains no rectangular cube coefficient.

`lowerFirstBlockIntegrationInput_of_sliceTower` obtains regularity from
compatibility of `νA` and sigma-finiteness from the second countable,
locally compact quotient. These provide the small measure's compact
finiteness and s-finiteness required by
`firstBlockSliceIntegration_of_comp`. That theorem supplies
`0 < d_k < ∞` and
`d_k = (ENNReal.ofReal (normalizedAbs (det v))) ^ b` on the small slice.
It then selects the actual s-finite first-block kernel, retaining its
everywhere representative measure law.

The analytic proof rewrites the measure identity and applies measure-bind
Tonelli. For measurable complex functions it separately removes the
positive finite scalar from integrability and applies
`Measure.integrable_comp_iff`. Consequently it proves both almost
everywhere fiber integrability and integrability of the fiber norm
integral. Under integrability, the pointwise equality between the
published unweighted `firstBlockAverage` and the kernel integral gives
outer integrability, almost everywhere strong measurability and the
Bochner law with scalar `d_k.toReal`.

## Closed assembly

`LowerFirstBlockSliceTowerInputStatement` records the geometric identity
with the target's exact measures; `LowerFirstBlockIntegrationInputStatement`
records its complete first-block analytic conclusion. Both are internal
Prop-valued definitions. Their hypotheses are discharged by the geometric
tower and analytic bridge before the final theorem applies
`assembleLowerFirstBlockQuotientIntegration`. The resulting theorem has
the closed target as its entire type.

The proof establishes absolute convergence through the stated integrability
equivalences, independently of equalities of total Bochner integrals.
Strong measurability of each total average is asserted almost everywhere
under integrability, as in the target. The implementation uses geometric
quotient integration and Haar scaling; it adds no representation,
character, uniformizer or convergence premises and uses no Section 7
assembly, Section 9.3 disintegration or later result depending on these
Section 4 inputs.
