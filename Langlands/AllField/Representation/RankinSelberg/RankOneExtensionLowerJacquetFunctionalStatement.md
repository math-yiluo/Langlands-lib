# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**An inverse-character functional on the lower induction given by absolutely convergent integrals**

JPSS (1983), proof of Lemma (5.5), printed page 424, formulas (1) and (3): the
Whittaker functional on the induced space is a limit of integrals of the scalar
coefficient of a section over the complementary unipotent subgroup against the
conjugate character `θ̄`, and `λ(σ(g) f)` is that integral itself where it converges
absolutely. This module only defines the proposition. It asks for one actual
inverse-character functional on the whole lower induced space that equals that
integral at every section and ambient element where the integrand is integrable. It
asserts no convergence.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionStableJacquetData`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement` (def): For every inverse-character Whittaker functional `ℓ` of `σ` and every self-dual
  Haar measure `ν`, there is one inverse-character Whittaker functional `Λ` of the actual
  lower induction `rankOneExtensionLowerModel F t χ σ` such that, for every section `f`
  and every `g`, `Λ (I(g) f)` equals the integral of
  `y ↦ ℓ(f(u(y) g)) ψ(y_last)` against the row product of `ν` whenever this integrand is
  integrable. No integrability is assumed or asserted for any particular `(f, g)`, and
  `Λ` is not claimed to be nonzero.
