# All-field port of `Langlands.Representation.Whittaker.TwoBlockOpenCell`

`Langlands.AllField.Representation.Whittaker.TwoBlockOpenCell` is the all-field port of the Library module `Langlands.Representation.Whittaker.TwoBlockOpenCell`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.Whittaker.TwoBlockOpenCell` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The concrete two-block cell of JPSS Proposition 9.1**

For positive ranks `A = a + 1` and `B = b + 1`, the cell `P w U'` of `GL_(A+B)`,
the restriction of the literal ordered canonical normalized upper induction of
`(π₁, π₂)` to the representatives `w n(x)`, and the submodule of induced
functions supported in the cell with compactly supported restriction. These
are concrete definitions and elementary laws only.

## Imports from the port

- `Langlands.AllField.Representation.Shahidi.Induction`

## Declarations

- `Langlands.AllField.Whittaker.twoBlockParabolic` (abbrev): The actual standard upper parabolic `P` of the ordered shape `(A, B)`.
- `Langlands.AllField.Whittaker.twoBlockCellPoint` (def): The representative `w n(x)`: the all-positive block Weyl matrix times the
  exchanged radical `U'(x)`, for `x` with `B` rows and `A` columns.
- `Langlands.AllField.Whittaker.twoBlockCell` (def): The cell `C = P w U'` of all products `q w n(x)` with `q ∈ P`.
- `Langlands.AllField.Whittaker.twoBlockInduced` (abbrev): The literal ordered representation `ξ` of the parent statement.
- `Langlands.AllField.Whittaker.twoBlockInducingRepresentation` (abbrev): The actual inducing representation of `P` on `V₁ ⊗ V₂`: the block tensor
  through the Levi projection, twisted by the positive half modulus.
- `Langlands.AllField.Whittaker.TwoBlockInducedCarrier` (abbrev): The carrier of `ξ`: the actual smooth covariant functions.
- `Langlands.AllField.Whittaker.twoBlockEval` (def): Evaluation of an element of the carrier of `ξ`, by `Induction.eval`.
- `Langlands.AllField.Whittaker.twoBlockRestriction` (def): The complex-linear restriction `f ↦ (x ↦ f(w n(x)))` to all tensor-valued
  functions of `x`.
- `Langlands.AllField.Whittaker.twoBlockCellSubmodule` (def): The submodule `D`: induced functions whose support lies in the cell and
  whose restriction to the representatives has compact support.
- `Langlands.AllField.Whittaker.twoBlockCellInclusion` (def): The injective linear inclusion `D → ξ`.
- `Langlands.AllField.Whittaker.twoBlockCellInclusion_apply` (theorem).
- `Langlands.AllField.Whittaker.twoBlockCellRestriction` (def): The restriction map on `D`.
- `Langlands.AllField.Whittaker.hasCompactSupport_twoBlockCellRestriction` (theorem): The restriction of an element of `D` has compact support.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.twoBlockShape`, `Langlands.Whittaker.mem_twoBlockCell_iff`, `Langlands.Whittaker.parabolic_mul_mem_twoBlockCell`, `Langlands.Whittaker.twoBlockCellPoint_mem`, `Langlands.Whittaker.blockWeyl_mem_twoBlockCell`, `Langlands.Whittaker.mul_mem_twoBlockCell`, `Langlands.Whittaker.mul_mem_twoBlockCell_iff`, `Langlands.Whittaker.twoBlockInduced_eq`, `Langlands.Whittaker.twoBlockEval_eq`, `Langlands.Whittaker.twoBlockEval_twoBlockInduced`, `Langlands.Whittaker.twoBlockRestriction_apply`, `Langlands.Whittaker.mem_twoBlockCellSubmodule_iff`, `Langlands.Whittaker.twoBlockCellInclusion_injective`, `Langlands.Whittaker.twoBlockCellRestriction_apply`, `Langlands.Whittaker.twoBlockEval_eq_zero_of_not_mem`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
