# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalysis`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAnalysis` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalysis`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAnalysis` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Auxiliary analysis for the two-block deformation**

General facts used to prove that the deformed Whittaker functions are entire:
an entire function vanishing on an uncountable set vanishes; the same for finite
exponential sums `∑ b_i^u • w_i` with positive real bases in any complex vector space;
the integral `u ↦ ∫_K α β^u` over a compact set with `β` positive and locally constant
is entire. It also records that the inverse standard character has open kernel, that
the upper unipotent group has an increasing exhaustion by compact open subgroups, and
that the rectangular matrices have an exhaustion by compact sets.

## Imports from the port

- `Langlands.AllField.Group.GL.UpperUnipotentCompactContainmentProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationNonvanishing`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.isOpen_ker_inverseStandardCharacter` (theorem): The inverse standard character of the upper unipotent group has open kernel.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_upperUnipotent_exhaustion` (theorem): The upper unipotent group has an increasing exhaustion by compact open subgroups.
- `Langlands.AllField.RankinSelberg.TwoBlockDeformation.exists_matrix_exhaustion` (theorem): The rectangular matrices over `F` have a sequence of compact sets eventually containing
  every compact set.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDeformation.exists_accPt_of_not_countable`, `Langlands.RankinSelberg.TwoBlockDeformation.eq_zero_of_not_countable`, `Langlands.RankinSelberg.TwoBlockDeformation.differentiable_ofReal_cpow`, `Langlands.RankinSelberg.TwoBlockDeformation.sum_cpow_smul_eq_zero_of_not_countable`, `Langlands.RankinSelberg.TwoBlockDeformation.differentiable_setIntegral_mul_cpow`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
