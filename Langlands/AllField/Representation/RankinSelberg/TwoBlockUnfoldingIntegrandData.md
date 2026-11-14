# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The integrand of the first Section 4.6 unfolding**

JPSS (1983), Section 4.6, equation (4) on printed page 411 and the first integral on
printed page 412: after substituting the Jacquet integral (4.6.2) into the outer integral
over `N_r \ G_r^m`, the iterated integrand is unfolded to the integral of
`W(g) f[g; e, e] Φ(η g)` over `N_(t_1,t_2) \ G_r^m`, where `N_(t_1,t_2)` is the
block-diagonal upper-unipotent group (5).

For two blocks of sizes `m 0 + 1` and `m 1 + 1` of total rank `t + 1`, actual block
functionals `ℓ_i` in the inverse-character spaces, a lower normalized section `f`, a test
function `W` in the standard-character space and a Schwartz–Bruhat function `Φ`, this
module constructs the scalar function

`[g]_H ↦ W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)`

on the published quotient `H \ GL_(t+1)`, `H = blockUnipotent h F`, by actual
quotient descent. It proves the block covariance of the scalar section, the left
`H`-invariance, the representative formula, the fiber formula through the positive
Jacquet kernel, and the identities of the total fiber integral and the radical average
with `W(g) J(f)(g) Φ(lastRow g)`. No integrability, measurability or Fubini statement is
asserted.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.scalarSection_blockEmbedding_mul` (theorem): Left translation by `diag(n_0, n_1)` multiplies the scalar section at the Levi identity
  by the product of the two block inverse standard characters `ψ⁻¹(n_0) ψ⁻¹(n_1)`.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.inverseStandardCharacter_blockEmbedding` (theorem): The product of the two block inverse standard characters of `(n_0, n_1)` is the
  ambient inverse standard character of `diag(n_0, n_1)`: the corner block vanishes.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter` (theorem): Left translation by `diag(n_0, n_1)` multiplies the scalar section at the Levi identity
  by the ambient inverse standard character of `diag(n_0, n_1)`.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.groupIntegrand` (def): The scalar function `g ↦ W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)` on `GL_(t+1)`, before
  descent.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.groupIntegrand_def` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.groupIntegrand_blockUnipotent_mul` (theorem): Left `H`-invariance: the standard character of `diag(n_0, n_1)` from `W` cancels the
  inverse character from the scalar section, and the last row is unchanged.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand` (def): The integrand of the first Section 4.6 unfolding on the actual quotient
  `N_(t_1,t_2) \ GL_(t+1)`: the actual descent of `groupIntegrand`. No coset representative
  is chosen.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_mk` (theorem): Representative formula: `integrand [g]_H = W(g) ⟨f(g), ⊗ ℓ_i⟩ Φ(lastRow g)`.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_fiberPoint` (theorem): The fiber formula: at `[u(x) g]_H` the standard covariance of `W` on the upper
  radical `u(x)` supplies the positive kernel `ψ(x_(m 0, 0))` of the raw Jacquet integrand.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.fiberIntegral_integrand` (theorem): The total fiber integral of the integrand over the rectangle, at a representative `g`,
  is `W(g) J(f)(g) Φ(lastRow g)` for the ordinary Bochner integral `J(f)(g)` of (4.6.2)
  against the same measure. This is an identity of total integrals: no integrability is
  assumed.
- `Langlands.AllField.RankinSelberg.TwoBlockUnfolding.radicalAverage_integrand_mk` (theorem): The published radical average of the integrand at `[g]_N` is
  `W(g) J(f)(g) Φ(lastRow g)`, for every Borel additive Haar measure on the rectangle.
  This is an identity of total integrals: no integrability is assumed.
