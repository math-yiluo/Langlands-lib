# All-field port of `Langlands.Representation.Induction.CompactScalarProof`

`Langlands.AllField.Representation.Induction.CompactScalarProof` is the all-field port of the Library module `Langlands.Representation.Induction.CompactScalarProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Induction.CompactScalarProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the scalar compact-picture integral for standard GL parabolics**

The compact open subgroup is the level-zero subgroup `GL_n(O_F)`, the factorization
`G = P K` is the Iwasawa decomposition, and the Haar probability measure on `K` is the
restriction of the mass-one Haar measure `generalLinearHaar` of `GL_n(F)`. The full Levi
modulus of the block parabolic is Mathlib's modular character of the parabolic, so the
invariance is the abstract compact averaging theorem.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusHaarProof`
- `Langlands.AllField.Representation.Induction.CompactScalarStatement`

## Declarations

- `Langlands.AllField.glParabolicCompactScalarIntegral` (theorem): **The scalar compact-picture integral.** For every standard block parabolic `P` of
  `GL_n(F)` with `n > 0`, the Haar probability measure on `K = GL_n(O_F)` integrates every
  locally constant function covariant on the left by the full modulus of `P` to a value
  invariant under all right translations.
