# Square-integrability modulo the full center on the literal Levi

This internal derived module links two square-integrability predicates
already in the Library. The Plancherel generic-irreducibility target uses
`IsSquareIntegrableModCentralSubgroup C hC π qMeasure`, where `C` is the image
of the split-component points in the literal Levi point subgroup
`parabolicLeviPointSubgroup p l`. The represented-parabolic results, such as
the Renard VII.2.4 criterion statement and the multiplicity results for the
geometric-lemma pieces, use `IsSquareIntegrableModCenter` on the Levi's own
rational points `M(F)` modulo the full abstract center. The module proves
that the first gives the second. It cites no external source.

The setting is that of the host target: a nonarchimedean local field `F`, an
affine `G` with canonical point topology, the actual maps `p`, `l`, `a`, and a
compatible root presentation `pres : ParabolicRootPresentation p l a`. Write
`e = parabolicLeviPointHomeomorph pres : M(F) ≃ₜ* parabolicLeviPointSubgroup p l`.

## Declarations

- `mulEquiv_mem_center`: a group isomorphism maps central elements to central
  elements. It follows from Mathlib's `Subgroup.map_center_eq`.
- `schemeCenterToParabolicCenter` (definition): the group homomorphism from the
  scheme-center points `schemeCenterPoints M` to the abstract center of the
  literal Levi point subgroup, `z ↦ e z`.
- `compactSpace_parabolicCenter_quotient`: the abstract center of the literal
  Levi point subgroup modulo `C` is compact. The published
  `centerSplitComponentCompactness` gives compactness of scheme-center points
  modulo the split-component image. The map induced by
  `schemeCenterToParabolicCenter` on the quotients is continuous. It is
  surjective because the published `rationalCenterComparison` identifies the
  scheme-center points with the abstract center of `M(F)`, and `e` is an
  isomorphism. So the target quotient is a continuous image of a compact space.
- `isClosed_parabolicSplitComponentPointHom_range`: `C` is closed in the
  literal Levi point subgroup. `C` is the preimage of the point image of the
  closed subgroup `a ≫ l ≫ p`, which is closed by the published
  `isClosed_pointImage`.
- `isSquareIntegrableModCenter_pullback_of_modCentralSubgroup`: assume `G` is
  connected reductive, `G(F)` is locally compact, nonarchimedean and Hausdorff,
  and `π` is square-integrable modulo `C` for a Haar measure `qMeasure`. Then
  the pullback of `π` along `e` is square-integrable modulo the center of
  `M(F)`, for every Haar measure on `M(F)` modulo its center. The proof
  applies the published `centralSubgroupCoefficientLpComparison` on the
  literal Levi point subgroup. Its inputs are: the point groups are
  second countable (published `reductiveRationalPoint_secondCountable`), the
  literal Levi is closed and hence locally compact, `C` is closed, and the
  center modulo `C` is compact. This gives square-integrability modulo the
  full center of the literal Levi for the pushforward of the chosen Haar
  measure along `centralQuotientCongr e`. The published
  `isSquareIntegrableModCenter_comp_continuousMulEquiv` then changes variables
  along `e`.

No hypothesis beyond the host target's own structural assumptions is used.
Temperedness, irreducibility and admissibility are not asserted, except that
admissibility is part of both square-integrability predicates.
