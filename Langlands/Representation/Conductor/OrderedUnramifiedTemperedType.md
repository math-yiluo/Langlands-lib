# Unramified principal series as standard modules of unitary rank-one blocks

Module `Langlands.Representation.Conductor.OrderedUnramifiedTemperedType`, namespace
`Langlands.Conductor.OrderedUnramifiedTemperedType`, over a nonarchimedean local field
`F` (instances `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, any
characteristic) with a uniformizing element `ϖ` and residue cardinality `q`.

The unramified character `χ_z` of `Fˣ` with `χ_z(ϖ) = z` (the published
`UnramifiedPrincipalSeries.character`) is written as `χ_w ν^v` with `w = z / |z|` of norm
one and `|z| = q^(-v)`. For `|x_1| ≤ ⋯ ≤ |x_(n+1)|` the exponents `v_j` are antitone, so
`I(x)` is the standard module of a datum of unitary, hence tempered, rank-one blocks
(`AllField.RankinSelberg.TemperedTypeDatum`).

## Contents

- `center_generalLinear_one`: the center of `GL_1(F)` is the whole group, so the central
  quotient of `GL_1(F)` is a point.
- `norm_character_eq_one`, `rankOneBlock_tempered`: the published rank-one block
  `OrderedUnramifiedRankOneBlocks.rankOneBlock ϖ w` with `‖w‖ = 1` is tempered in the
  sense of `IsTemperedRepresentation`. Its central character is the character itself,
  which has norm one, and every function on the one-point central quotient lies in every
  `L^p` of the finite Haar measure.
- `rankOneBlock_whittaker`: the rank-one block is of Whittaker type for every `ψ` (the
  published all-field `rankOneCharacter_isOfWhittakerType`, through the identification of
  `ULift ℂ` with `ℂ`).
- `unitaryPart z = z / |z|`, `norm_unitaryPart`, `realExponent q z = -log_q |z|`,
  `realExponent_antitone`, `one_lt_of_isResidueCardinality`.
- `character_unitaryPart_mul`: `χ_(z/|z|)(a) · |a|^(realExponent q z) = χ_z(a)`, with the
  normalized absolute value `|a| = q^(-ord a)` (published
  `AllField.Conductor.UnramifiedPrincipalSeries.normalizedAbs_units`).
- `unramifiedDatum hϖ n hq x hx`: the datum with the singleton block shape
  (`AllField.Conductor.UnramifiedPrincipalSeries.borelBlocks n`), blocks
  `rankOneBlock ϖ (x_j / |x_j|)` and exponents `realExponent q (x_j)`.
- `unramifiedDatum_twistedBlockEquiv`, `unramifiedDatum_standardModuleEquiv`: each twisted
  block is the rank-one character `χ_(x_j)`, and the standard module is the published
  principal series `principalSeries ϖ n hq x`
  (published all-field `AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv`).
- `pointDatum hϖ hq z`, `pointDatum_standardModuleEquiv`: the one-block datum of `χ_z`, whose
  standard module is the rank-one character `rankOneCharacter (character ϖ z)`
  (published all-field `singleBlockNormalizedProductEquiv`).

Source: the description of `I(t)` as an induced representation and of its parameters in
Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`), printed pages 516–517,
and the use of `I(t)` as a representation of Langlands' type in JPSS 1983 (literature ID
`jpss-1983-rankin-selberg`), (9.4), printed page 458. Temperedness of unitary characters
of `GL_1` is the definition of temperedness applied to a one-point central quotient.
