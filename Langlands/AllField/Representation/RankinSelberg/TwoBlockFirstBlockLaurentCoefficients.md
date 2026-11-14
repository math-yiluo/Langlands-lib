# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentCoefficients`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentCoefficients` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentCoefficients`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentCoefficients` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The two large first-block coefficients as row integrals of small coefficients**

At a fixed representative `g`, the rectangular average over the lower radical of the upper
first-block average on the slice `k` is the row integral of `Φ((x, η) g)` times the
slice coefficient `k` of the original small integral of the translate by `R(0; x) g`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.upper_coefficient_eq_rowIntegral` (theorem): The upper coefficient at a representative: under absolute convergence of the iterated
  fiber integral, it is the row integral of `Φ((x, η) g)` times the original small slice
  coefficient of the translate by `R(0; x) g` and the first-block coefficient of `f(g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.integrable_rowRestriction` (theorem): The row restriction `x ↦ Φ((x, η) g)` of a Schwartz–Bruhat function is integrable.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.lower_slice_scalar` (theorem): On the small slice `k`, the lower density `q^(-k b)`, the inverse half modulus and the
  Jacobian `|det v|⁻¹` combine to `q^k` times the transformed small determinant weight.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.lower_coefficient_eq_rowIntegral` (theorem): The lower coefficient at a representative: the lower density times the first-block
  average on the slice `k` is the row integral of `Φ((x, η) g)` times the reflected series
  of the transformed small slice coefficients of the translate by `R(0; x) g`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.ae_lintegral_kernel_comp_lt_top`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
