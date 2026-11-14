# All-field port of `Langlands.Representation.GodementJacquet.WhittakerIwasawaReduction`

`Langlands.AllField.Representation.GodementJacquet.WhittakerIwasawaReduction` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.WhittakerIwasawaReduction`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.WhittakerIwasawaReduction` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Iwasawa reduction of full-matrix Whittaker integrals**

The analytic properties of a Whittaker function `W` on `GL_(n+1)(F)` used for
the convergence and rationality of `∫ Φ(g) W(g) |det g|^s dg`, and the first
reduction steps: Iwasawa integration `G = N A K` in the canonical
normalization, the factorization of the integrand at `u diag(a) k`, its
unipotent integral as a slice integral of `Φ`, and the finite coset sum over
`K`. See the paired Markdown.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerCosetSum`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerSliceSchwartz`
- `Langlands.AllField.Representation.GodementJacquet.WhittakerTorusMellin`
- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement`
- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaHaarIntegration`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankIwasawaSupportProof`
- `Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof`

## Declarations

- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.integralK` (abbrev): The integral subgroup `K = GL_(n+1)(O)`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.borelModulus` (def): The upper-Borel modulus `δ(a) = ∏_{i<j} |a_i / a_j|`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.HasTorusExpansion` (def): A torus expansion `f(a) = Σ_{χ ∈ X} φ_χ(a_0/a_1, …, a_(n-1)/a_n) χ(a)`, with a
  finite set `X` of finite functions and Schwartz–Bruhat coefficients `φ_χ`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.IsWhittakerLike` (structure): The properties of a function `W` on `GL_(n+1)(F)` used to prove convergence
  and rationality of its full-matrix integrals: continuity, left equivariance
  under the standard character of the upper unipotent group, right invariance
  under an open subgroup, and a torus expansion of every right translate.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.lintegral_iwasawa` (theorem): **Iwasawa integration**, lower Lebesgue form:
  `∫_G f = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.integral_iwasawa` (theorem): **Iwasawa integration**, Bochner form for integrable complex functions.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.normalizedAbs_det_integralK` (theorem): The normalized absolute value of the determinant of an element of `K` is one.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.matrixIntegrand_iwasawa` (theorem): The matrix integrand at `u diag(a) k`, for `k ∈ K` and a left-equivariant
  `W`, is `(W(diag(a) k) |∏ a_i|^s) · (Φ(u diag(a) k) ψ_N(u))`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.integral_unipotent_matrixIntegrand` (theorem): The unipotent integral of the matrix integrand at `u diag(a) k`, for
  `k ∈ K`, is `W(diag(a) k) |∏ a_i|^s` times the slice integral of `Φ(· k)`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.lintegral_unipotent_matrixIntegrand` (theorem): The unipotent integral of the norm of the matrix integrand at `u diag(a) k`,
  for `k ∈ K`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.matrixIntegrand_mul_right` (theorem): The matrix integrand is right invariant under `k₀ ∈ K` fixing `Φ` and `W`.
- `Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.IsWhittakerLike.exists_cosetSum` (theorem): **Finite coset reduction.** For `W` as in `IsWhittakerLike` and a test
  function `Φ`, there are an open subgroup `K₀ ≤ K` and a finite set `S ⊆ K` such
  that the matrix integrand is right invariant under `K₀` for every `s`, and the
  integral over `K` of every right-`K₀`-invariant function is the sum of its
  values on `S` times the mass of `K₀`.
