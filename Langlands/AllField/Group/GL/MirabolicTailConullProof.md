# All-field port of `Langlands.Group.GL.MirabolicTailConullProof`

`Langlands.AllField.Group.GL.MirabolicTailConullProof` is the all-field port of the Library module `Langlands.Group.GL.MirabolicTailConullProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Group.GL.MirabolicTailConullProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the open full-measure inverse-row tail locus**

Openness follows from continuity of inversion and of matrix entries. The
exceptional set is covered by finitely many pieces with a nonzero head
coordinate; an elementary transvection with a small nonzero parameter moves
each piece off itself, so Steinhaus's theorem makes each piece null.
See the paired Markdown for the full route.

## Proof route

The proof of `Langlands.AllField.padic_exists_ne_zero_mem_nhds_zero` differs from its original. The original finds a nonzero element in a neighbourhood `U` of zero as the image of a nonzero element of `Padic p` near zero under the continuous algebra map `ℚ_[p] → F`; a field of positive characteristic has no such map. The port uses the valuative topology instead: `U` contains a ball `{x | v x < v a}` with `a ≠ 0` (`IsValuativeTopology.hasBasis_nhds_zero'`), the valuation is nontrivial, so some `r` has `0 < v r < 1`, and then `a * r` is a nonzero element of the ball. The statement is unchanged.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.Group.GL.PadicBlocksSupplement`

## Declarations

- `Langlands.AllField.GeneralLinear.padic_exists_ne_zero_mem_nhds_zero` (theorem): Every neighbourhood of zero in the supplied topology contains a nonzero
  element. A neighbourhood of zero contains a valuation ball `{x | v x < v a}` with
  `a ≠ 0`; multiplying `a` by an element of valuation less than one (the valuation is
  nontrivial) gives a nonzero element of that ball.

Public declarations of the original that are not re-declared here: `Langlands.GeneralLinear.haar_null_of_forall_nhds_disjoint_translate`, `Langlands.GeneralLinear.transvectionUnit_zero`, `Langlands.GeneralLinear.inv_transvectionUnit_mul_apply_same`, `Langlands.GeneralLinear.exists_inv_apply_ne_zero`, `Langlands.GeneralLinear.continuous_transvectionUnit`, `Langlands.GeneralLinear.padicMirabolicTailConull`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
