# Gamma stability outside a finite set for the two Hecke families

Supporting module for the proof of `AssociatedGammaStatement` (module
`Langlands.Automorphic.AssociatedGammaOutsideStability`). This module supplies the
`OutsideGammaStability` input of the two-twist engine (`HeckeTwistComparisonStatement`) for the
automorphic and arithmetic Hecke families of the modules `Langlands.Automorphic.AssociatedGammaAutomorphicFamily` and
`Langlands.Automorphic.AssociatedGammaArithmeticFamily`. The proof uses the published
`PrincipalSeriesPairGammaMatchStatement` (Henniart 1986 §2.7(iii); Jacquet–Piatetski-Shapiro–Shalika
1983, Theorem 3.1) and the local genericity statement `CuspidalLocalGenericityStatement`, both as
hypotheses here. Both are proved in the Library (`principalSeriesPairGammaMatchStatement`,
`Automorphic.CuspidalPairPartialGamma.localGenericity`); `AssociatedGammaFinal` supplies them.

## Results

- `exists_principalSeries_localClass`: let `z` be outside the exceptional set of a presentation
  `P`. Then there is a tuple `x` of Satake parameters, whose unordered spectrum is the spectrum of
  `P` at `z`, and a representative of the local class of `P` at `z`. The representative is generic
  for any given `ψ` (by `hGen`) and is a subquotient of the unramified principal series
  `i(character x_1, …, character x_(r+1))`. Proof: the presentation supplies the Hecke spectrum of
  the local component (`hasSpectrum`). `hasSphericalHeckeSpectrumClass_iff` moves it to the p-adic
  object, and `hasSphericalSpectrum_of_hasSphericalHeckeSpectrum` gives the principal series.
- `exists_localComponent_basis`: let `S₀ ∘ ι` be unramified with Euler polynomial
  `∏ (1 - x_i X)` and rank `n`. Then there are a basis of the carrier of `S₀` and a permutation `σ`
  such that every `S₀(ι g)` is upper triangular, with diagonal entries `x_(σ i) ^ deg g`. This is
  `Weil.Local.exists_triangular_basis_of_eulerPolynomial`.
- `outsideGammaStability_families`: assume `hPS`, `hGen` and `hEps`, matching additive
  characters, `rank S = r + 1`, `rank S' = t + 1`, and a finite set `T`. Outside `T`, both
  presentations must be unramified and `S`, `S'` must match their Euler polynomials
  (`IsUnramifiedMatchAt`). Then for every finite-order Hecke character `χ` and every finite
  place `z ∉ T`, the gamma factors of the two families at `z` agree as germs. Proof:
  - The PS statement is applied at `z` with the base reciprocity candidate of the local family
    (geometric by `isGeometricReciprocity_of_isBaseReciprocity`) and the characters
    `μ_i = character(x_i) · χ_z` and `μ'_j = character(x'_j) · 1`.
  - Classes: `π_z ⊗ χ_z` (from `exists_generic_subquotient_twist`) and `π'_z` (the same lemma
    with the trivial twist).
  - Arithmetic representatives: the zero-monodromy classes of `(S ∘ ι) ⊗ (χ_z ∘ τ)` and `S' ∘ ι`.
  - The diagonal entries follow from `weilCharacter_apply_of_isUnramified` and
    `character_uniformizer`: `x_(σ i) ^ deg g · χ_z(τ(g))`.
  - The resulting `IsPairGammaMatch` gives equal gamma factors by
    `meromorphicEq_gamma_of_isPairGammaMatch`.
