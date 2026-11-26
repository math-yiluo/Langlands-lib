# The torus, its cosets and the orbit map

The module `Langlands.Analysis.Local.WeylChartGroups` defines the group-level coordinate maps
near a unit `γ` of a normed algebra `R` over a nontrivially normed field `F`.

## Definitions

- `unitOf a`: the unit with value `a` when `a` is a unit, and `1` otherwise
  (`val_unitOf`, `unitOf_of_not_isUnit`). It is used to turn ring-valued coordinates into
  units.
- `torusGroup γ`: the centralizer `Subgroup.centralizer {γ}` of `γ` in `Rˣ`
  (`mem_torusGroup_iff`: `u γ = γ u` in `R`). It contains `γ` (`self_mem_torusGroup`).
  `unitOf (1 + s)` lies in it for every `s` in the centralizer subalgebra
  (`unitOf_mem_torusGroup`).
- `torusChart γ s = unitOf (1 + s) · γ`, a torus element, for `s` in the centralizer
  subalgebra.
- `cosetChart γ y`: the coset in `LeftQuotient (torusGroup γ)` of `(unitOf (1 + y))⁻¹`, for
  `y` in the image of the adjoint defect.
- `orbitCoord γ (y, s) = (cosetChart γ y, torusChart γ s)`.
- `orbitMap hcomm`: for a subgroup `H` of `Rˣ` whose elements commute with each other (the
  hypothesis `hcomm`), the map `(H x, h) ↦ x⁻¹ h x` on `LeftQuotient H × H`. It is well
  defined on cosets because conjugation of `h` by an element of `H` is trivial.
  `orbitMap_mk` records its value on a representative.

With `torusGroup γ` for `H` and small units `1 + y`, `1 + s`, the value of
`orbitMap (orbitCoord γ (y, s))` is `(1 + y)(1 + s) γ (1 + y)⁻¹`. So the orbit map in these
coordinates is the conjugation chart of `Langlands.Analysis.Local.WeylChartMaps` followed by
right multiplication by `γ` (`orbitMap_orbitCoord` in
`Langlands.Analysis.Local.WeylChartLocal`). The ordinary Weyl map of
Henniart–Lemaire (2011), II.2.10, is `orbitMap` for the rational points of a maximal torus.
