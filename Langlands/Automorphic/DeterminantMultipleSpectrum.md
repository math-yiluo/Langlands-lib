# Spherical spectra of determinant multiples

Author: Worker 5137.

This helper module of the proof
`Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation`
proves the automorphic half of the argument. Suppose the realization of `T'` is the
determinant multiple of the realization of `T` by a Hecke character `χ` of arbitrary
order (`OperatorRealization.IsDeterminantMultiple`: a linear equivalence
`e : T.Space ≃ₗ[ℂ] T'.Space` whose continuous functions satisfy
`T'.toContinuous (e f) = (g ↦ χ(det g) · f(g))`). Then at every finite place `v` where
`χ` is unramified and both presentations are unramified, the spectrum of `T'` at `v` is
the spectrum of `T` with every Satake parameter multiplied by `χ_v(ϖ_v)`. Consequently the
scaled spectral system of a presentation `P` of `T` and the spectral system of any
presentation `P'` of `T'` have the same Euler polynomials at almost every place. This is
the unramified part of Henniart (2000), §2.2, for twists by `χ ∘ det`.

## `HeckeCharacter.finiteLocalDeterminant_eq_one_of_isUnramifiedAt`

If `χ` is unramified at `v` and `g ∈ GL_n(F_v)` lies in `localIntegral F n v`
(`g` and `g⁻¹` have integral entries, that is `g ∈ GL_n(𝒪_v)`), then
`χ_v(det g) = 1`. By `finiteLocalDeterminant_eq_finiteComponent_det` the value is
`χ_v(det g)`; the determinants of `g` and `g⁻¹` are integral (the determinant of a matrix
over the subring `𝒪_v`, `RingHom.map_det`), so `det g` is a unit of `𝒪_v`, where `χ_v`
is trivial by `IsUnramifiedAt`.

## Determinant multiples and translations (namespace `OperatorRealization`)

- `toContinuous_finiteRepresentation`: the continuous function of the finite translate
  `S.finiteRepresentation d f` is the right translate of the continuous function of `f`
  by `d` (embedded in the adelic group). Both are the same function, checked pointwise.
- `finiteRepresentation_of_toContinuous_eq`: if `e` realizes `T` as the determinant
  multiple of `S` by `χ`, then
  `T.finiteRepresentation d (e f) = χ(det d) · e (S.finiteRepresentation d f)`. Since
  `T.toContinuous` is injective, compare continuous functions: right translation of
  `χ(det) · F` by `d` is `χ(det d) · χ(det) · (right translate of F)`
  (`determinantMultiplier_rightAction`); the computation is written as an explicit chain
  of equalities.
- `localRepresentation_of_toContinuous_eq`: the same for the local translations at `v`:
  `T.localRepresentation v g (e f) = χ_v(det g) · e (S.localRepresentation v g f)`, the
  previous lemma at `d = localInclusion F n v g`.

## Spectra (namespace `CuspidalOperatorRealization`)

- `eigenvalues_eq_scale_of_isDeterminantMultiple`: let `T, T'` be cuspidal realizations
  with presentations `P, P'`, let the realization of `T'` be the determinant multiple of
  that of `T` by `χ`, and let `v` be a finite place with `χ` unramified at `v` and `v`
  outside the exceptional sets of `P` and `P'`. Then
  `P'.spectralSystem.eigenvalues v = Eigenvalues.scale (χ.finiteUniformizerValue v)
  (P.spectralSystem.eigenvalues v)`.

  Proof. Take a nonzero spherical vector `a` of the local restriction of `T` at `v`
  (`CuspidalSpectralPresentation.exists_spherical_ne_zero`). By irreducibility, on every
  spherical vector of the local restrictions of `T` and `T'` the standard Hecke elements
  act by the scalars of the presented spectra
  (`CuspidalSpectralPresentation.corner_eq_smul`). Apply the abstract lemma
  `Langlands.Unramified.PairedHecke.eq_scale_of_twist` (module `TwistedHeckeScalars`) to
  the local restrictions of `T` and `T'`, the equivalence `e`, and
  `ψ = χ_v ∘ det = χ.finiteLocalDeterminant (r + 1) v`: the twist relation is
  `localRepresentation_of_toContinuous_eq`; triviality of `ψ` on `GL_(r+1)(𝒪_v)` is
  `finiteLocalDeterminant_eq_one_of_isUnramifiedAt` together with
  `localIntegral_eq_sphericalSubgroup`; and `ψ(standardDiagonal i) = χ_v(ϖ_v) ^ i` is the
  Library lemma `finiteLocalDeterminant_standardDiagonal`.
- `sameEulerPolynomials_scale_of_isDeterminantMultiple`: under the determinant-multiple
  hypothesis, `SpectralSystem.scale χ.finiteUniformizerValue P.spectralSystem` and
  `P'.spectralSystem` have the same Euler polynomials. A Hecke character is unramified
  outside a finite set (`HeckeFunctionalEquation.exists_finset_isUnramifiedAt`); at every
  other place outside both exceptional sets the eigenvalues agree by the previous lemma.
