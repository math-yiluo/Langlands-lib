# Principal-series constituents and their character twists

Supporting module of Task 5003 (module `Langlands.Automorphic.AssociatedGammaPrincipalSeries`).
It supplies the automorphic hypotheses of the published
`PrincipalSeriesPairGammaMatchStatement` for twists of unramified local components. Standard
representation theory.

## Results (namespace `Langlands.Correspondence`)

- `isSubquotientOf_of_equiv_left`: if `ρ ≃ ρ'` and `π` is a subquotient of `ρ` (in the sense of
  `IsSubquotientOf`), then `π` is a subquotient of `ρ'`. The subrepresentation is pulled back
  along `e⁻¹`, and the surjection is precomposed with `e⁻¹`.
- `isSubquotientOf_twist`: twisting both representations by a common character `χ : G →* ℂˣ`
  preserves the subquotient relation. The same submodule and the same linear surjection work.
- `quasiSmoothCharacter`: a quasi-character of `K^×` regarded as an
  `Induction.SmoothCharacter` (open kernel by `RankinSelberg.quasicharacter_isOpen_ker`).
- `characterBlockTwistEquiv`: on `GL_1`, the twist of `μ ∘ det` by `η ∘ det` is `(μ η) ∘ det`;
  the equivalence is the identity of `ℂ`.
- `principalSeriesTwistEquiv`: `(η ∘ det) ⊗ i(μ_1, …, μ_(r+1)) ≃ i(μ_1 η, …, μ_(r+1) η)` for the
  normalized principal series `principalSeries K r μ`. This is the composition of the published
  `normalizedProductDeterminantTwistEquiv` (multiply induced functions by `η(det g)`) with
  `normalizedProductInducedEquiv` applied to the blockwise equivalences.
- `exists_generic_subquotient_twist`: let `π` have a representative that is generic for `ψ` and
  a subquotient of `i(μ)`, and let `πη` be the twist of `π` by `η` (`IsCharacterTwist`). Then
  `πη` has a representative that is generic for `ψ` and a subquotient of `i(μ η)`. Genericity
  is preserved by the twist (`RankinSelberg.isGeneric_quasicharacter_twist`) and by
  equivalences (`Whittaker.isGeneric_iff_of_equiv`). The subquotient property follows from the
  three results above.

## Results (namespace `Langlands.Unramified`)

- `hasSphericalSpectrum_of_hasSphericalHeckeSpectrum`: if an irreducible admissible object `A`
  has spherical Hecke spectrum `s`, then `A` is a spherical subquotient of an unramified
  principal series with unordered spectrum `s` (`HasSphericalSpectrum`). The proof repeats the
  published proof of `sphericalSpectrumExistence` with the given `s`. Choose a tuple `z` with
  spectrum `s` and a spherical constituent `B` of `i(z)`. `B` has Hecke spectrum `s` by
  `sphericalConstituentHeckeScalar`. Then `A ≃ B` by `sphericalHeckeSpectrumDetermination`.
