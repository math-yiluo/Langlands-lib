# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Fixed-slice absolute convergence and the first Section 4.6 unfolding**

JPSS (1983), Section 4.6, printed pages 411-412. For two blocks of full standard
Whittaker type, twisted by `|det|^(-u)` and `|det|^u`, the source substitutes the Jacquet
integral (4.6.2) into the outer integral (4) over `N_r \ G_r^m` and unfolds it to the
integral of `W(g) f[g; e, e] Φ(η g)` over `N_(t_1,t_2) \ G_r^m`, justified by the compact
support of `W(g) Φ(η g)` on `G_r^m` modulo `N_r`.

This module states, for every real `u` above one bound depending on the block data, the
measurability, fiber and fixed-slice absolute integrability, and the normalized restricted
Bochner identity for the published integrand on the actual quotient
`N_(t_1,t_2) \ GL_(t+1)`, together with the representative formula for its radical average.
The test representation is every smooth representation with an actual coefficient image,
which is a derived strengthening of the source's Whittaker-type test representation. This
is a proposition definition; no proof is supplied.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement`
- `Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement` (def): JPSS (1983), Section 4.6, printed pages 411-412, fixed-slice form. The rectangular
  integral-cube mass `c` of the supplied self-dual product measure is positive and finite,
  the right-invariance certificates hold and compatible quotient measures on `N \ G` and
  `H \ G` exist. For blocks `τ` of full standard Whittaker type and every pair of supplied
  inverse-character functionals `ℓ`, there is a real bound `C` such that for every `u > C`,
  every section `f` of the actual lower induction of `(τ_0 |det|^(-u), τ_1 |det|^u)`, every
  actual coefficient image `W` of a smooth test representation, every row Schwartz–Bruhat
  function `Φ` and every integer `k`, the published integrand `E` on `H \ G` and its radical
  averages are measurable, every rectangular fiber of `E` is integrable, the radical average
  of `E` at `[g]` is `W(g) J(f)(g) Φ(lastRow g)`, and for every compatible pair of quotient
  measures `E` is integrable on the determinant-`k` slice of `H \ G`, its absolute and signed
  radical averages are integrable on the determinant-`k` slice of `N \ G`, and the restricted
  integral of the radical average is `c` times the restricted integral of `E`.
