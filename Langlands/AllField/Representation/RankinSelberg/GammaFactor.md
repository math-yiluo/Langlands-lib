# All-field port of `Langlands.Representation.RankinSelberg.GammaFactor`

`Langlands.AllField.Representation.RankinSelberg.GammaFactor` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.GammaFactor`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.GammaFactor` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Gamma factors of pairs as relations on JPSS functional equations**

`IsPairGammaFactor` says that the rational function `G` of `q^(-s)` is the
gamma factor `γ(s, π × σ, ψ)` of Henniart 1993 (2.3.4)-(2.3.5): the dual
integral at `1 - s` is `ζ^e G(q^(-s))` times the integral at `s`, for every
compatible quotient measure and every pair of nonzero Whittaker functionals.
No factor function is chosen and existence is not assumed. Uniqueness and
invariance under equivalence are proved.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.IsPadicPairGammaFactor` (def): The gamma-factor relation for actual representations of `GL_(r+1)(F)` and
  `GL_(n+1)(F)` over a p-adic field with its canonical topological data: `q` is
  the residue cardinality and the absolute value is the normalized one.
- `Langlands.AllField.RankinSelberg.IsPadicPairGammaFactor.unique` (theorem): The p-adic gamma factor is unique.
- `Langlands.AllField.RankinSelberg.IsPadicPairGammaFactor.congr_equiv` (theorem): The p-adic gamma-factor relation is invariant under representation
  equivalences.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.GammaFunctionalEquation`, `Langlands.RankinSelberg.GammaFunctionalEquation.gamma_unique`, `Langlands.RankinSelberg.EqualRankGammaEquation`, `Langlands.RankinSelberg.EqualRankGammaEquation.congr_model`, `Langlands.RankinSelberg.EqualRankGammaEquation.unique`, `Langlands.RankinSelberg.EqualRankGammaEquation.functionalPullback_iff`, `Langlands.RankinSelberg.UnequalRankGammaEquation`, `Langlands.RankinSelberg.UnequalRankGammaEquation.congr_model`, `Langlands.RankinSelberg.UnequalRankGammaEquation.unique`, `Langlands.RankinSelberg.UnequalRankGammaEquation.functionalPullback_iff`, `Langlands.RankinSelberg.IsEqualRankGammaFactor`, `Langlands.RankinSelberg.IsUnequalRankGammaFactor`, `Langlands.RankinSelberg.IsPairGammaFactor`, `Langlands.RankinSelberg.IsEqualRankGammaFactor.unique`, `Langlands.RankinSelberg.IsEqualRankGammaFactor.of_equiv`, `Langlands.RankinSelberg.IsEqualRankGammaFactor.congr_equiv`, `Langlands.RankinSelberg.IsUnequalRankGammaFactor.unique`, `Langlands.RankinSelberg.IsUnequalRankGammaFactor.of_equiv`, `Langlands.RankinSelberg.IsUnequalRankGammaFactor.congr_equiv`, `Langlands.RankinSelberg.isPairGammaFactor_of_lt`, `Langlands.RankinSelberg.isPairGammaFactor_self`, `Langlands.RankinSelberg.not_isPairGammaFactor_of_lt`, `Langlands.RankinSelberg.IsPairGammaFactor.unique`, `Langlands.RankinSelberg.IsPairGammaFactor.of_equiv`, `Langlands.RankinSelberg.IsPairGammaFactor.congr_equiv`, `Langlands.RankinSelberg.IsClassGammaFactor`, `Langlands.RankinSelberg.isClassGammaFactor_mk`, `Langlands.RankinSelberg.IsClassGammaFactor.unique`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
