# All-field port of `Langlands.Representation.CuspidalSupport.HarishChandraConverseProof`

`Langlands.AllField.Representation.CuspidalSupport.HarishChandraConverseProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.HarishChandraConverseProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.HarishChandraConverseProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact smooth-dual coefficients on `G°` imply quasicuspidality**

Proof of `Langlands.AllField.CuspidalSupport.LeviHarishChandraConverseTheorem`, BZ76
Theorem 3.21, (4) implies (1).

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Representation.CuspidalSupport.HarishChandraConverseStatement`
- `Langlands.AllField.Representation.Geometric.RefinementDefinitions`
- `Langlands.AllField.Representation.Jacquet.BlockPowerKernelProof`

## Declarations

- `Langlands.AllField.CuspidalSupport.HarishChandra.exists_strictlyContracting_determinantNorm_eq_one` (theorem): A strictly contracting block-scalar tuple whose block scalar has
  determinant of normalized absolute value one.
- `Langlands.AllField.CuspidalSupport.HarishChandra.eventually_blockScalar_pow_notMem` (theorem): Powers of a strictly contracting block scalar with at least two blocks
  eventually leave every compact subset of the general linear group.
- `Langlands.AllField.CuspidalSupport.HarishChandra.compressedAction_blockScalar_pow` (theorem): Powers of a weakly contracting block scalar compress multiplicatively.
- `Langlands.AllField.CuspidalSupport.HarishChandra.mulSingle_mem_determinantUnitSubgroup` (theorem): A tuple supported on one block lies in `G°` when that block does.
- `Langlands.AllField.CuspidalSupport.HarishChandra.isLeviQuasicuspidal_of_hasCompactSmoothDualCoefficients` (theorem): BZ76 Theorem 3.21, (4) ⇒ (1): if every coefficient of the restriction to `G°`
  against a smooth dual vector has compact support, the representation is
  quasicuspidal on the product Levi.
- `Langlands.AllField.CuspidalSupport.leviHarishChandraConverseTheorem` (theorem): BZ76 Theorem 3.21, (4) implies (1), on actual local-field product Levis.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.HarishChandra.exists_eq_zero_of_eventually_dual`, `Langlands.CuspidalSupport.HarishChandra.averageMap_apply_mem`, `Langlands.CuspidalSupport.HarishChandra.orbit_pi_eq_orbit_single`, `Langlands.CuspidalSupport.HarishChandra.exists_two_le_length_of_refinedParabolic_ne_top`, `Langlands.CuspidalSupport.HarishChandra.relations_mulSingle_le`, `Langlands.CuspidalSupport.HarishChandra.blockScalar_const`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
