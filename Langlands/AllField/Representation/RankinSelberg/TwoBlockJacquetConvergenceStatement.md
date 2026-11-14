# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Ordinary absolute convergence of the two-block Jacquet integral**

JPSS 1983, Section (4.6), printed pages 410-411. For representations `τ_1, τ_2`
of Whittaker type of `GL_(m_0+1)(F)` and `GL_(m_1+1)(F)`, put
`σ_1 = τ_1 ⊗ α^(-u)` and `σ_2 = τ_2 ⊗ α^u` with `α = |det|` and `u` real. The
source asserts that for `u ≫ 0` the integral (4.6.2) of every section of the
lower induction `Ind(G_t, Q; σ_1 × σ_2)` converges. This module states that
assertion as ordinary absolute integrability of the published raw integrand
of `Langlands.Representation.RankinSelberg.TwoBlockJacquetData`, at every
ambient element, for every real `u` above one bound. It proves no convergence.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData`

## Declarations

- `Langlands.AllField.RankinSelberg.twoBlockOppositeTwistBlocks` (abbrev): The blocks of JPSS (4.6) at the real parameter `u`: the first block is twisted
  by `|det|^(-u)` and the second by `|det|^u`, on the same carriers.
- `Langlands.AllField.RankinSelberg.twoBlockOppositeTwistBlocks_apply` (theorem): The action of a twisted block is the scalar `|det g|^(∓u)` times the original action.
- `Langlands.AllField.RankinSelberg.determinantComplexPower_upperUnipotent` (theorem): Every determinant power is trivial on the upper unipotent subgroup.
- `Langlands.AllField.RankinSelberg.twoBlockOppositeTwistBlocks_isOfWhittakerType_iff` (theorem): The twisted blocks have full Whittaker type for a character exactly when the
  original blocks do.
- `Langlands.AllField.RankinSelberg.twoBlockOppositeTwistFunctional` (def): A supplied inverse-character functional of `τ i` is, with the same linear map,
  an inverse-character functional of the twisted block.
- `Langlands.AllField.RankinSelberg.twoBlockOppositeTwistFunctional_val` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockJacquetConvergenceStatement` (def): JPSS 1983, Section (4.6), printed pages 410-411: for blocks `τ_1, τ_2` of full
  standard Whittaker type and supplied nonzero inverse-character functionals
  `ℓ_1, ℓ_2`, there is a real bound `C` such that for every real `u > C` and every
  section `f` of the actual lower induction of `(τ_1 |det|^(-u), τ_2 |det|^u)`, the
  raw integrand `x ↦ (ℓ_1 ⊗ ℓ_2)(f(u(x) g)) ψ(x_(m_0,0))` of (4.6.2) is integrable
  for the product of the supplied self-dual Haar measure, at every ambient `g`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.twoBlockOppositeTwistBlocks_zero`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
