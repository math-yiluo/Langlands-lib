# All-field port of `Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement`

`Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field, carrying either bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`) or the corresponding instances (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`. Declarations that take explicit data `T : F.TopologicalData` in the original take explicit data `T : LocalFieldData F` in the port.

Source: the original module `Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Lower-block disintegration of the left-unipotent quotient**

The determinant density `[g] ↦ |det g|^(-d)` on `N_a \ GL_a`, defined by actual
quotient descent, and the proposition that every compatible quotient measure on
`N_(a+d) \ GL_(a+d)` is a positive multiple of the pushforward, under the published
lower-block chart `([g], x, h) ↦ [[[g,0],[x,h]]]`, of the weighted product
`D μ_a × dx × ρ` with `ρ` a right Haar measure on `B⁻_d` (JPSS §9.3, printed 456).
The proposition is stated, not proved.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.lowerBlockDensity_unipotent_mul` (theorem): The representative weight `|det g|^(-d)` is invariant under left
  multiplication by `N_m`, since upper-unipotent matrices have determinant one.
- `Langlands.AllField.RankinSelberg.lowerBlockQuotientDensity` (def): The actual determinant density `[g] ↦ |det g|^(-d)` on `N_m \ GL_m`,
  with the residue-normalized absolute value of `T`, defined by quotient descent.
- `Langlands.AllField.RankinSelberg.lowerBlockQuotientDensity_mk` (theorem).
- `Langlands.AllField.RankinSelberg.continuous_lowerBlockQuotientDensity` (theorem): The density is continuous for the quotient topology.
- `Langlands.AllField.RankinSelberg.measurable_lowerBlockQuotientDensity` (theorem): The density is Borel measurable on the quotient.
- `Langlands.AllField.RankinSelberg.LowerBlockQuotientDisintegrationStatement` (def): Lower-block disintegration of the actual left-unipotent quotient, in ranks
  `a = n + 1`, `d = k + 1` and `a + d`. For compatible quotient measures `μa` and
  `μad`, the published chart `([g], x, h) ↦ [[[g,0],[x,h]]]` is an open measurable
  embedding with `μad`-conull range, and there are a right Haar measure `ρ` on the
  lower-triangular group and a constant `C > 0` with
  `μad = C • map chart ((μa.withDensity D).prod (dx.prod ρ))`,
  `D [g] = |det g|^(-d)`, together with the resulting integrability and integral
  transfer for Borel measurable complex functions.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.lowerBlockQuotientDensity_ne_top`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
