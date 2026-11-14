# All-field supplement to `Langlands.AllField.Representation.RankinSelberg.DeterminantSlices`

`Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement` supplements the Library module `Langlands.AllField.Representation.RankinSelberg.DeterminantSlices`, the existing all-field port of `Langlands.Representation.RankinSelberg.DeterminantSlices`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.RankinSelberg.DeterminantSlices` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.DeterminantSlices` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Determinant slices and equal-rank slice coefficients**

JPSS (1983), Section 4.2, (4.2.1): the determinant fibers `|det g| = q^(-m)` of
the actual quotient `N_(n+1) \ GL_(n+1)` and the restricted integrals over them.
The measure is supplied. No convergence, support bound, compactness, or series
expansion of the full integral is asserted.

## Imports from the port

- `Langlands.AllField.Group.GL.UnramifiedCharacterSupplement`
- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlices`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange`

## Declarations

- `Langlands.AllField.RankinSelberg.determinantOrder` (def): JPSS (4.2.1) quotient determinant order: `q ↦ ord(det g)` for any representative
  `g` of `q ∈ N_(n+1) \ GL_(n+1)`. Independence uses `det u = 1` for upper unipotent `u`.
- `Langlands.AllField.RankinSelberg.determinantOrder_mk` (theorem).
- `Langlands.AllField.RankinSelberg.determinantSlice` (def): JPSS (4.2.1) determinant slice `N_(n+1) \ G^m`, where `G^m = {g | |det g| = q^(-m)}`,
  written through the quotient determinant order.
- `Langlands.AllField.RankinSelberg.mem_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.mk_mem_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.mk_mem_determinantSlice_iff_normalizedAbs` (theorem): Slice membership of a representative is the source condition `|det g| = q^(-m)`
  for the residue-normalized absolute value.
- `Langlands.AllField.RankinSelberg.continuous_determinantOrder` (theorem): The quotient determinant order is continuous into the discrete integers.
- `Langlands.AllField.RankinSelberg.isClopen_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.isOpen_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.isClosed_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.measurableSet_determinantSlice` (theorem): Every slice is measurable for any Borel structure on the actual quotient.
- `Langlands.AllField.RankinSelberg.disjoint_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.pairwise_disjoint_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.iUnion_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.determinantOrder_rightTranslate` (theorem): Right translation by `g` shifts the quotient determinant order by `ord(det g)`.
- `Langlands.AllField.RankinSelberg.rightTranslate_mem_determinantSlice` (theorem).
- `Langlands.AllField.RankinSelberg.sliceCoefficient` (def): The restricted coefficient `m ↦ ∫_{S_m} f dμ` over the determinant slices, for a
  supplied measure on the Borel structure of the quotient. This is the general form of
  JPSS (4.2.1).
- `Langlands.AllField.RankinSelberg.SliceIntegrableAt` (def): Integrability of `f` on the single slice `S_m`, for the Borel structure.
- `Langlands.AllField.RankinSelberg.sliceIntegrableAt_iff` (theorem).
- `Langlands.AllField.RankinSelberg.SliceIntegrable` (def): Integrability of `f` on every determinant slice, for the Borel structure.
- `Langlands.AllField.RankinSelberg.sliceIntegrable_of_integrable` (theorem): Global integrability implies integrability on every slice.
- `Langlands.AllField.RankinSelberg.sliceCoefficient_smul` (theorem): Scalar multiplication needs no integrability hypothesis.
- `Langlands.AllField.RankinSelberg.sliceCoefficient_eq_integral_indicator` (theorem): Each coefficient is the full integral of the indicator of the (Borel) slice.
- `Langlands.AllField.RankinSelberg.equalRankSliceCoefficient` (def): JPSS (4.2.1): `Ψ^m(W, W'; Φ) = ∫_{N \ G^m} W(g) W'(g) Φ(η g) dg`, realized as the
  slice coefficient of the equal-rank integrand at `s = 0` for the normalized
  absolute value. The measure `μ` is supplied on the Borel structure of the quotient.
- `Langlands.AllField.RankinSelberg.equalRankSliceCoefficient_def` (theorem).
- `Langlands.AllField.RankinSelberg.equalRankIntegrand_eq_mul_spectralPoint_zpow` (theorem): On the slice `S_m`, the integrand at `s` is its value at zero times
  `(q^(-s))^m`, with `q` the residue cardinality and integer exponent `m`.
- `Langlands.AllField.RankinSelberg.setIntegral_equalRankIntegrand_determinantSlice` (theorem): The restricted integral at `s` over `S_m` is the `m`-th coefficient times
  `(q^(-s))^m`. No integrability is needed for this identity of Bochner integrals.
- `Langlands.AllField.RankinSelberg.sliceIntegrableAt_equalRankIntegrand_iff` (theorem): Slice integrability of the integrand at `s` is equivalent to that at zero.

Declarations of the original re-declared by `Langlands.AllField.Representation.RankinSelberg.DeterminantSlices` and therefore not here: `Langlands.RankinSelberg.continuous_ord_units`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.determinant_unipotent_mul`, `Langlands.RankinSelberg.determinantWeight_zero`, `Langlands.RankinSelberg.equalRankIntegrand_zero_mk`, `Langlands.RankinSelberg.sliceCoefficient_def`, `Langlands.RankinSelberg.SliceIntegrableAt.add`, `Langlands.RankinSelberg.SliceIntegrableAt.smul`, `Langlands.RankinSelberg.SliceIntegrable.add`, `Langlands.RankinSelberg.SliceIntegrable.smul`, `Langlands.RankinSelberg.sliceCoefficient_add`, `Langlands.RankinSelberg.sliceCoefficient_add_fun`, `Langlands.RankinSelberg.sliceCoefficient_smul_fun`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
