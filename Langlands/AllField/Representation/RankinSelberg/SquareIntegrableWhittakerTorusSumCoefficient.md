# All-field port of `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient`

`Langlands.AllField.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Whittaker values on the antidominant torus cone as smooth matrix coefficients**

For a smooth representation `π` of `GL_(m+1)(F)`, a Whittaker functional `ℓ` and a
vector `v`, there are a positive principal level `K(r)` fixing `v` and a smooth
functional `L`, fixed by `K(r)`, such that `L (π(ϖ^lam) v) = ℓ (π(ϖ^lam) v)` for every
antitone exponent vector `lam`. The functional is the average
`L w = ∫_{K(r)} ℓ (π(g⁻¹) w) dg` for the Haar measure of unit mass on `K(r)`; the Iwahori
factorization of `K(r)` shows that the integrand is constant on the antitone cone.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement`
- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Group.GL.CompactOpenSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.SquareIntegrableWhittakerTorusSum.exists_smooth_eq_on_antitone` (theorem): For a smooth representation of `GL_(m+1)(F)`, a standard Whittaker functional `ℓ`, a
  vector `v` and an element `ϖ` of valuation at most one, there are a positive principal level
  `K(r)` fixing `v` and a smooth functional `L`, invariant under `K(r)`, with
  `L (π(ϖ^lam) v) = ℓ (π(ϖ^lam) v)` for every antitone exponent vector `lam`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.isLocallyConstant_apply_inv`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.integrableOn_apply_inv`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.averagedFunctional`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.averagedFunctional_apply`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.averagedFunctional_apply_mul`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.averagedFunctional_mem_fixedVectors`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.averagedFunctional_mem_smoothVectors`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.averagedFunctional_apply_of_forall`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.torus_conj_upper_mem`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.torus_inv_conj_lower_mem`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.torus_commute_levi`, `Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum.apply_inv_torus_eq`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
