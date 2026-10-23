# Tower identities for idele-class cohomology

This module defines the proposition
`Langlands.ClassField.Global.IdeleClassCohomologyTowerLaws.{u}`.
It groups three identities for the actual maps constructed in
`CohomologyMaps`. The coefficient group is the idele class group of the upper
field with its arithmetic Galois action, and cohomology is Mathlib's ordinary
group cohomology. The module states the identities; it does not prove them.

All fields belong to the same universe `u` and are number fields. Each
four-field tower carries all six algebra structures and all four scalar-tower
compatibilities. Each identity is quantified over every natural cohomological
degree `n`, including zero, and every class in its source.

- `IdeleClassRestrictionTransitivity` uses a tower `F → K → L → E`
  with `E/F` Galois. Restricting from `Gal(E/F)` to `Gal(E/K)` and then
  to `Gal(E/L)` equals direct restriction to `Gal(E/L)`.
  Both routes retain the coefficient group `C_E`.
- `IdeleClassInflationTransitivity` uses a tower `F → E → L → M`
  with `E/F`, `L/F`, and `M/F` Galois. Inflation from `Hⁿ(E/F,C_E)`
  to `Hⁿ(L/F,C_L)` followed by inflation to `Hⁿ(M/F,C_M)` equals
  direct inflation from `E` to `M`. These maps use normal restriction of
  automorphisms and the actual idele-class inclusions.
- `IdeleClassInflationRestrictionCompatibility` uses a tower
  `F → K → E → L` with `E/F` and `L/F` Galois. Inflating from `E/F`
  to `L/F` and then restricting the base to `K` equals restricting from
  `E/F` to `E/K` and then inflating to `L/K`. The Galois instance for
  `E/K` is explicitly derived from that for `E/F`.

Their conjunction is `IdeleClassCohomologyTowerLaws`.
No invariant map, injectivity, exactness, cardinality assertion, or vanishing
theorem is a premise or conclusion.

## Provenance

This is a derived supporting statement for the global invariant construction.
Artin and Tate, *Class Field Theory* (2009), Chapter XIV §2, printed
pp.148–149 (PDF pp.157–158), use transitivity of inflation to identify classes
in larger normal layers, then display the commuting inflation–restriction
square. The resulting restriction between limiting cohomology groups is used
in the construction of invariants in XIV §3, printed pp.152–153.

The formal statement records the same finite-layer identities using the
Library's actual arithmetic maps. It also records restriction transitivity
and extends the identities from degree two to every ordinary cohomological
degree. This extension is a formal consequence of composition of the
underlying group and coefficient maps: Mathlib's
`groupCohomology.map_comp` and `groupCohomology.map_congr` express exactly
that functoriality. It is not presented as an additional all-degree theorem
quoted from the cited pages. The shared-universe number-field scope matches
the published `CohomologyMaps` interface.

Registered source: `artin-tate-2009-class-field-theory`, SHA-256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
