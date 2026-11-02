# Local-field units for Plancherel character evaluation

Author: Worker 200.

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.1, printed p.103 (PDF p.109), fixes the surjective normalized additive order,
the integer-unit group, the actual residue cardinality `q`, and the normalized
absolute value `|x|_F = q ^ (-v_F(x))`. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d’après
Harish-Chandra)*, I.1, printed p.240 (PDF p.6), uses the same sign in
`q ^ (-⟨χ,H_G(g)⟩) = |χ(g)|_F`. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

This file supplies units and sign adapters for these conventions. It reuses the
published `Langlands.LocalField.ResidueNormalization` and `Langlands.FML.ord`.
The field, valuation, integer-unit subgroup, residue field, residue cardinality
and absolute value are those existing objects. No new field or valuation
structure is introduced. The packaging as homomorphisms on units and the sign
comparison are derived consumer adapters for character evaluation.

The hypotheses are exactly

`F : Type uF`, `[Field F] [ValuativeRel F] [TopologicalSpace F]`
`[IsNonarchimedeanLocalField F]`.

There is no characteristic, finite-extension-of-ℚ_p or splitness restriction.
The field universe is arbitrary. The residue cardinality is
`Langlands.LocalField.residueCardinality F`, not an independent parameter.
Its value exceeds one by the published theorem.

- `fieldNormUnits F : Fˣ →* ℝ≥0ˣ` is the restriction of the actual
  residue-normalized absolute value to field units. It uses `Units.map` on
  the composite of the published normalized multiplicative valuation with
  Mathlib’s `WithZeroMulInt.toNNReal` at the actual residue cardinality.
  `fieldNormUnits_val` identifies the real value with
  `LocalField.residueNormalizedAbsoluteValue F (a : F)`.
- `fieldOrderUnits F : Fˣ →* Multiplicative ℤ` is the pointwise inverse of
  the existing
  `NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationUnitsMulHom F`.
  That existing map has the multiplicative-value-group sign. Inversion in
  `Multiplicative ℤ` negates its integer coordinate, giving the source’s
  positive order of a uniformizer. `fieldOrderUnits_toAdd` identifies the
  coordinate as the negative logarithm of the published normalized
  multiplicative valuation, and `fieldOrderUnits_ord` proves that its cast
  to `WithTop ℤ` equals the already defined `FML.ord` at the nonzero field
  element. Thus the adapter agrees with the existing order rather than
  replacing it. No convention at the zero field element is introduced by
  a map defined only on units.
- `fieldNormUnits_zpow` gives the actual normalization formula with integer
  exponent. `fieldNormUnits_rpow` gives the same formula using real
  exponentiation, in the orientation needed by the normalized-logarithm
  construction.
- `fieldNormUnits_eq_one_iff` proves that these two actual maps have exactly
  the same unit kernel. `fieldOrderUnits_ker` and `fieldNormUnits_ker` identify
  both actual homomorphism kernels with the existing integral-unit subgroup
  `FML.unitGroup F`.
- `fieldOrderUnits_surjective` proves that every integer occurs on actual
  field units, using the published realization of every finite `FML.ord`
  value and constructing a unit from the resulting nonzero field element.

The sign proof applies `WithZero.logEquiv_apply` to the units valuation and
compares with `FML.ord_of_ne_zero`. The normalization follows from the
published `residueNormalizedAbsoluteValue_of_ord_eq`, followed by the standard
comparison of integer and real powers. Since the actual `q` exceeds one,
`zpow_eq_one_iff_right₀` gives equality of the unit kernels. The integral-unit
kernel identification then uses `FML.mem_unitGroup_iff_ord_eq_zero`.
These are intrinsic comparisons and laws of the constructed adapters.

The file constructs neither rational algebraic characters nor their evaluation
on group-scheme points. Those must be imported from the shared algebraic-group
program and composed with these actual field-unit maps. It asserts no
continuity or local constancy of these maps, no rational-point group topology,
no image-lattice or split-center theorem, and no character-torus or Haar
normalization. In particular, it does not discharge the whole Plancherel
structural requirement WST-NORM-01 or the retained logarithm/lattice obligation.
