# Continuity of the actual normalized local-field maps

Author: Worker 1218.

`Langlands.Plancherel.fieldUnitsTopology.{uF}` proves exactly the published
`Langlands.Plancherel.FieldUnitsTopologyStatement.{uF}`. For every
`F : Type uF` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`, it proves all five conclusions: continuity
of `LocalField.residueNormalizedAbsoluteValue F` on the whole field,
local constancy and continuity of `fieldOrderUnits F`, and local constancy
and continuity of `fieldNormUnits F`. The field universe and characteristic
are unrestricted. All maps, residue cardinalities and topologies are the
existing ones imported from the unchanged target and its dependencies.

The governing normalization is Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 edition, V.1, printed pp.103–104
(PDF pp.109–110): the normalized order, an order-one uniformizer, the actual
finite residue field of cardinality `q`, the absolute value `q^(−v_F(x))`,
and the valuative neighborhoods of zero. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard V.2.3, printed pp.105–106 (PDF pp.111–112), motivates the use of
these field maps in rational-character orders and smooth norm characters.
Waldspurger 2003, I.1, printed pp.239–240 (PDF pp.5–6), uses the normalized
absolute value and the negative exponent in the definition of `H_G`;
registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
These passages were read. They explain the target's provenance; the Lean
proof below is a derived argument from the existing Library and pinned
Mathlib, rather than a formalization of an additional literature theorem.

The private helper `normalizedAbsoluteValue_mono` shows that comparison of
the canonical multiplicative valuation implies comparison of the actual
normalized absolute values. It composes the monotonicity of the existing
`valueGroupWithZeroIsoInt F` with
`WithZeroMulInt.toNNReal_strictMono` at the actual residue cardinality,
which exceeds one, and then uses the order-preserving coercion to the reals.

`continuous_residueNormalizedAbsoluteValue` treats zero and nonzero points
separately. At zero, for any positive real radius `ε`,
`exists_pow_lt_of_lt_one` chooses `n : ℕ` such that `(q⁻¹)^n < ε`.
The existing `LocalField.uniformizer F` is nonzero and has order one, so
its `n`th power has nonzero valuation and normalized absolute value
`(q⁻¹)^n`. The canonical valuation ball of this radius is a neighborhood
of zero by `IsValuativeTopology.hasBasis_nhds_zero'`. Monotonicity bounds
the absolute value throughout that ball by `(q⁻¹)^n`, proving the required
metric target convergence. This uses only the real target's metric and
the supplied field topology; it selects no replacement field topology.
At a nonzero point, `Valuation.locally_const` supplies a neighborhood on
which the canonical valuation is constant. The monotonicity helper in both
directions makes the normalized absolute value constant on that
neighborhood, which proves continuity there.

The private helper `units_valuation_isLocallyConstant` pulls back these
nonzero valuation fibers along `Units.continuous_val` for the standard
unit-group topology and packages them with
`IsLocallyConstant.iff_eventually_eq`. Every field unit is nonzero.
`fieldOrderUnits_isLocallyConstant` then uses the published
`fieldOrderUnits_toAdd`: equal canonical valuations have equal normalized
valuations, hence equal negative logarithms and equal integer orders.
`fieldNormUnits_isLocallyConstant` uses the existing
`fieldNormUnits_zpow` to pass equality of integer orders to equality of
real normalized norms. Injectivity of the nonnegative-real coercion and
`Units.ext` recover equality in `ℝ≥0ˣ`.
`fieldOrderUnits_continuous` and `fieldNormUnits_continuous` each apply
`IsLocallyConstant.continuous`. Finally, `fieldUnitsTopology` collects the
five results in the exact target conjunction.

There is no local-constancy claim at the zero field element. No new
normalization, discreteness assumption, characteristic-zero hypothesis
or rational-point topology is introduced. Algebraic-character evaluation
continuity, common-kernel openness, image-lattice results, split-center
comparisons, character tori and measures remain separate obligations.
The target pair and all its imported pairs are unchanged. This module
adds only the proof and its supporting theorems. The inspection of the
closing theorem reports the single universe parameter `uF` and only
`propext`, `Classical.choice` and `Quot.sound` as axioms.
