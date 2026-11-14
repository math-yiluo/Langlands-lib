# All-field port of `Langlands.Group.GL.LowerTriangularBigCellConull`

`Langlands.AllField.Group.GL.LowerTriangularBigCellConull` is the all-field port of the Library module `Langlands.Group.GL.LowerTriangularBigCellConull`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Group.GL.LowerTriangularBigCellConull` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The lower big cell `N · B⁻` is conull**

For an invertible matrix `g`, write `A_k(g)` for the matrix agreeing with `g`
on the rows and columns of index at least `k` and with the identity elsewhere,
so that `det A_k(g)` is the bottom-right minor of size `m - k`. Then `g = u b`
with `u` upper unipotent and `b` invertible lower triangular exactly when all
these minors are nonzero. The complement of `N · B⁻` is closed and null for
every left Haar measure: it is covered by finitely many pieces, each moved off
itself by an elementary transvection with a small nonzero parameter. A
compatible quotient measure on `N \ G` vanishes on every measurable set whose
preimage is Haar-null, so the cosets not represented by `B⁻` form a null set.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpenSupplement`
- `Langlands.AllField.Group.GL.MirabolicTailConullProof`

## Declarations

- `Langlands.AllField.GeneralLinear.padic_setOf_not_upperUnipotent_mul_lowerTriangular` (theorem): In the supplied topology, the complement of `N · B⁻` in `GL_m(F)` is closed
  and null for every left Haar measure.
- `Langlands.AllField.GeneralLinear.padic_lowerTriangular_leftQuotient_conull` (theorem): For every compatible quotient measure on `N_m \ GL_m(F)`, in the supplied
  topology, the cosets with no representative in `B⁻` form a null set.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.bottomCornerMatrix`, `Langlands.GeneralLinear.bottomCornerMatrix_apply`, `Langlands.GeneralLinear.bottomCornerMatrix_apply_of_le`, `Langlands.GeneralLinear.bottomCornerMatrix_apply_of_lt_right`, `Langlands.GeneralLinear.bottomCornerMatrix_row_of_lt`, `Langlands.GeneralLinear.bottomCornerMatrix_mul_apply_of_lt`, `Langlands.GeneralLinear.bottomCornerMatrix_mul`, `Langlands.GeneralLinear.det_bottomCornerMatrix_of_mem_upperUnipotent`, `Langlands.GeneralLinear.det_bottomCornerMatrix_ne_zero_of_mem_lowerTriangular`, `Langlands.GeneralLinear.det_bottomCornerMatrix_mul_ne_zero`, `Langlands.GeneralLinear.exists_upperUnipotent_mul_lowerTriangular`, `Langlands.GeneralLinear.exists_upperUnipotent_mul_lowerTriangular_iff`, `Langlands.GeneralLinear.setOf_not_upperUnipotent_mul_lowerTriangular_eq`, `Langlands.GeneralLinear.bottomCornerMatrix_eq_one`, `Langlands.GeneralLinear.bottomCornerExchange`, `Langlands.GeneralLinear.det_bottomCornerMatrix_transvection_mul`, `Langlands.GeneralLinear.exists_bottomCornerExchange_ne_zero`, `Langlands.GeneralLinear.continuous_bottomCornerMatrix`, `Langlands.GeneralLinear.continuous_det_bottomCornerMatrix`, `Langlands.GeneralLinear.continuous_bottomCornerExchange`, `Langlands.GeneralLinear.isClosed_setOf_not_upperUnipotent_mul_lowerTriangular`, `Langlands.GeneralLinear.haar_setOf_not_upperUnipotent_mul_lowerTriangular`, `Langlands.QuotientIntegration.IsCompatible.measure_eq_zero_of_preimage`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
