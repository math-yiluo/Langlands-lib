# A right-invariant measure on the unipotent quotient of the mirabolic group

Author: Worker 805.

This helper module provides, for a nonarchimedean local field `F` and every
rank `n`, a measure `ν` on the published left quotient
`QuotientIntegration.LeftQuotient (Mirabolic.upperUnipotent n F)`, that is on
`N \ P` for the mirabolic group `P = mirabolic n F` (inside `GL_(n+1)`) and its
upper unipotent subgroup `N`, with the three properties used by
`Langlands.Induction.FormsFunctional` (`exists_measure`):

- `IsFiniteMeasureOnCompacts ν`;
- right invariance: `MeasurePreserving (rightTranslate _ g) ν ν` for every `g : P`;
- for every compact open subgroup `J` of `P`, the orbit
  `compactOpenQuotientOrbit _ J` has positive finite mass.

The Borel structure on the quotient is supplied by the caller
(`[MeasurableSpace …] [BorelSpace …]`). The construction is internal (derived):
the measure is transported from the Library's published `GL` quotient measure.

## The quotient homeomorphism (section `Homeomorph`)

`projection : P_n → GL_n` (upper-left block) maps `N` into the upper unipotent
group of `GL_n` (`projection_mem_upperUnipotent`), and the Levi embedding
`levi : GL_n → P_n` maps upper unipotent matrices into `N`
(`levi_mem_upperUnipotent`), by comparing matrix entries. The induced maps on
left cosets, `toGL` and `ofGL` (`Quotient.map'`), are continuous
(`Continuous.quotient_map'` with `continuous_projection`, `continuous_levi`) and
mutually inverse: `projection (levi a) = a`, and
`g · levi (projection g)⁻¹` is the radical matrix `radicalElement (lastColumn g)`
(`eq_radicalElement_mul_levi`), which lies in `N` (`radical_le_upperUnipotent`).
This gives `quotientHomeomorph : N \ P ≃ₜ N_GL \ GL_n`. Since `projection` is a
homomorphism, it intertwines right translation by `g` with right translation by
`projection g` (`quotientHomeomorph_rightTranslate`,
`rightTranslate_quotientHomeomorph_symm`).

## The measure

- **Rank zero** (`exists_measure_zero`). `mirabolic 0 F` is trivial
  (`Mirabolic.rankOneSubsingleton`), so the quotient is a single point. The Dirac
  measure at the identity coset is finite, every right translation is the
  identity map, and every orbit contains the identity coset, so it has mass one.
- **Positive rank** (`exists_measure_succ`). For `n = k + 1`, `ν` is the image of
  the published `RankinSelberg.unipotentQuotientHaar F k` (on the unipotent
  quotient of `GL_(k+1)`, with Borel structures on the groups and quotient) under
  the inverse homeomorphism. It is finite on compacts because the published
  measure is regular and the map is a homeomorphism
  (`IsFiniteMeasureOnCompacts.map`). Right invariance follows from the
  intertwining relation and the published right invariance of
  `unipotentQuotientHaar` (`unipotentQuotientHaar_isCompatible`, field
  `right_invariant`), by `Measure.map_map`. The mass of an orbit of a compact
  open `J` is the published measure of its image under the homeomorphism, a
  nonempty compact open set; it is positive and finite by
  `IsCompatible.measure_pos_lt_top`.

`exists_measure` combines the two cases.
