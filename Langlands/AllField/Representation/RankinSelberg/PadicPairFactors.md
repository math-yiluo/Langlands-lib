# All-field port of `Langlands.Representation.RankinSelberg.PadicPairFactors`

`Langlands.AllField.Representation.RankinSelberg.PadicPairFactors` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.PadicPairFactors`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.PadicPairFactors` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Pair factors of actual p-adic representations**

Uniqueness and equivalence invariance of the epsilon-factor relation
`IsPadicPairEpsilonFactor` of a p-adic field with its canonical topological
data; the L-polynomial relation `IsPadicPairLPolynomial` over the published
`IsPairLPolynomial`, quantified over every compatible quotient measure; and the
gamma, epsilon and L relations `IsPadicSymmetricGammaFactor`,
`IsPadicSymmetricEpsilonFactor`, `IsPadicSymmetricLPolynomial` for pairs of
either rank order, with the
convention of JPSS (2.12) (printed page 403) that the pair is read with the
larger rank first.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.GammaFactor`
- `Langlands.AllField.Representation.RankinSelberg.LocalConverseStatement`
- `Langlands.AllField.Representation.RankinSelberg.PairLFactor`

## Declarations

- `Langlands.AllField.RankinSelberg.IsPadicPairLPolynomial` (def): `P` is the L-polynomial of the pair `(π, σ)` of actual representations of
  `GL_(r+1)(F)` and `GL_(n+1)(F)` over a p-adic field with its canonical
  topological data: a compatible quotient measure exists, and for every compatible
  quotient measure `P` is the published pair L-polynomial `IsPairLPolynomial`,
  with `q` the residue cardinality and the normalized absolute value.
- `Langlands.AllField.RankinSelberg.IsPadicPairLPolynomial.unique` (theorem): The p-adic L-polynomial of a pair is unique.
- `Langlands.AllField.RankinSelberg.IsPadicPairLPolynomial.congr_equiv` (theorem): The p-adic L-polynomial relation is invariant under representation
  equivalences.
- `Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor` (def): `γ(s, π × σ, ψ) = G(q^(-s))` for actual representations `π` of `GL_(r+1)(F)`
  and `σ` of `GL_(n+1)(F)` of either rank order. When `n ≤ r` it is the pair
  relation `IsPadicPairGammaFactor` for `(π, σ)`; when `r < n` it is the pair
  relation for `(σ, π)`. This is the convention of JPSS (2.12), printed page 403:
  a pair is read with the larger rank first.
- `Langlands.AllField.RankinSelberg.IsPadicSymmetricEpsilonFactor` (def): `ε(s, π × σ, ψ) = c q^(-ms)`, `e = (c, m)`, for actual representations `π`
  of `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)` of either rank order, with the same
  convention as `IsPadicSymmetricGammaFactor`.
- `Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial` (def): `L(s, π × σ) = 1 / P(q^(-s))` for actual representations `π` of
  `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)` of either rank order, with the same
  convention as `IsPadicSymmetricGammaFactor`.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricGammaFactor_of_le` (theorem).
- `Langlands.AllField.RankinSelberg.isPadicSymmetricGammaFactor_of_lt` (theorem).
- `Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.unique` (theorem): The gamma factor of a pair of either rank order is unique.
- `Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv` (theorem): The gamma relation for either rank order is invariant under representation
  equivalences.
- `Langlands.AllField.RankinSelberg.isPadicSymmetricEpsilonFactor_of_le` (theorem).
- `Langlands.AllField.RankinSelberg.isPadicSymmetricLPolynomial_of_le` (theorem).
- `Langlands.AllField.RankinSelberg.isPadicSymmetricLPolynomial_of_lt` (theorem).
- `Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.unique` (theorem): The L-polynomial of a pair of either rank order is unique.
- `Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv` (theorem): The L relation for either rank order is invariant under representation
  equivalences.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.IsPadicPairEpsilonFactor.unique`, `Langlands.RankinSelberg.IsPadicPairEpsilonFactor.congr_equiv`, `Langlands.RankinSelberg.isPadicSymmetricEpsilonFactor_of_lt`, `Langlands.RankinSelberg.IsPadicSymmetricEpsilonFactor.unique`, `Langlands.RankinSelberg.IsPadicSymmetricEpsilonFactor.congr_equiv`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
