# All-field port of `Langlands.Representation.RankinSelberg.MultiplicativityStatement`

`Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.MultiplicativityStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.MultiplicativityStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Multiplicativity of the factors of pairs**

JPSS 1983, Theorem (3.1), printed pages 404-405: for `π` of Whittaker type on
`GL_r(F)` and `σ = Ind(σ_1, …, σ_p)` induced from representations of Whittaker
type on the blocks of a standard parabolic of `GL_t(F)`, the gamma factor of
`π × σ` is the product of the gamma factors of `π × σ_i`, and
`L(s, π × σ)` lies in `∏ L(s, π × σ_i) ℂ[q^(-s), q^s]`. The factors are the
relations `IsPadicSymmetricGammaFactor` and `IsPadicSymmetricLPolynomial` with
the self-dual measure, which cover both rank orders. The induced
representation is the published normalized induction
`canonicalNormalizedProductInduced` from the standard upper block parabolic.

## Imports from the port

- `Langlands.AllField.Representation.Induction.BlockFactors`
- `Langlands.AllField.Representation.RankinSelberg.PadicPairFactors`

## Declarations

- `Langlands.AllField.RankinSelberg.GammaMultiplicativityStatement` (def): JPSS 1983, Theorem (3.1)(i) (printed page 405). Let `π` be a representation
  of Whittaker type of `GL_(r+1)(F)`, and `σ_1, …, σ_k` representations of
  Whittaker type of `GL_(m_i + 1)(F)` with `∑ (m_i + 1) = t + 1`. Then each pair
  `(π, σ_i)` has a gamma factor `G_i`, and their product is the gamma factor of
  `π` against the normalized induction of `(σ_1, …, σ_k)` to `GL_(t+1)(F)`.
- `Langlands.AllField.RankinSelberg.LFactorMultiplicativityStatement` (def): JPSS 1983, Theorem (3.1)(ii) (printed page 405), with the hypotheses of
  `GammaMultiplicativityStatement`: the L-polynomials `P` of `π` against the
  induced representation and `P_i` of `(π, σ_i)` exist, and
  `L(s, π × σ) ∈ ∏ L(s, π × σ_i) ℂ[q^(-s), q^s]`, that is,
  `X^e ∏ P_i = Q P` for a polynomial `Q` and some `e`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.succBlockShape`, `Langlands.RankinSelberg.MultiplicativityStatement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
