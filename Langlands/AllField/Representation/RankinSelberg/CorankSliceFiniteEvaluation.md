# All-field port of `Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation`

`Langlands.AllField.Representation.RankinSelberg.CorankSliceFiniteEvaluation` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.CorankSliceFiniteEvaluation` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite evaluation of corank-one determinant slices with common compact support**

JPSS (1983), Section 4.5, printed pages 408–409. Suppose a family of standard
Whittaker functions on `GL_(r+2)` is right invariant under one open subgroup and
depends analytically on a parameter at each point, and suppose the restrictions to
one determinant slice of all corank-one integrands against a fixed coefficient
on `GL_(r+1)` vanish outside one compact set. Then one compact open subgroup `J`
of `GL_(r+1)` leaves every integrand and the slice invariant, finitely many
pairwise disjoint `J`-orbits carry all the restricted integrands, and each slice
integral is a finite sum of orbit masses times point values, with orbits and
masses independent of the parameter. Hence every slice is integrable and its
coefficient is analytic. The common compact support is a hypothesis here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.CorankOneEntireSliceStatement`
- `Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant`

## Declarations

- `Langlands.AllField.RankinSelberg.CommonLevel.ord_det_of_mem_integralSubgroup` (theorem): An integral invertible matrix has determinant of order zero.
- `Langlands.AllField.RankinSelberg.CommonLevel.corank_slice_of_common_support` (theorem): JPSS (1983), Section 4.5, printed pages 408–409, in the corank-one setting,
  conditional on common compact support. Let `U` be a family of standard Whittaker
  functions on `GL_(r+2)` right invariant under one open subgroup `K` and analytic in
  the parameter at each point, and `Wprime` a fixed coefficient of a representation of
  Whittaker type on `GL_(r+1)`. If on the slice `S_m` every corank-one integrand at
  `s = 0` vanishes outside one compact set `C`, then each of these integrands is
  integrable on `S_m` and the slice coefficient is analytic in the parameter.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.CommonLevel.rightTranslateOrbit`, `Langlands.RankinSelberg.CommonLevel.self_mem_rightTranslateOrbit`, `Langlands.RankinSelberg.CommonLevel.rightTranslateOrbit_eq_of_mem`, `Langlands.RankinSelberg.CommonLevel.disjoint_rightTranslateOrbit`, `Langlands.RankinSelberg.CommonLevel.rightTranslateOrbit_mk`, `Langlands.RankinSelberg.CommonLevel.isOpen_rightTranslateOrbit`, `Langlands.RankinSelberg.CommonLevel.isCompact_rightTranslateOrbit`, `Langlands.RankinSelberg.CommonLevel.exists_finset_rightTranslateOrbit_cover`, `Langlands.RankinSelberg.CommonLevel.integrableOn_and_setIntegral_eq_sum_rightTranslateOrbit`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
