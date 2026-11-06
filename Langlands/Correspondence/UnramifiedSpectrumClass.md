# Unramified parameter classes of spectra

This is an internal helper module. It attaches to every unordered spectrum
`s : Unramified.Eigenvalues (r + 1)` the unramified Frobenius-semisimple
parameter class `unramifiedSpectrumClass F s` of rank `r + 1`, whose geometric
Frobenius lift has eigenvalues `s`, with multiplicities. It proves that every
unramified parameter class of rank `r + 1` arises in this way from exactly one
spectrum, and that the standard Euler polynomial `parameterEulerPolynomial F D`
of `Langlands/Correspondence/UnramifiedEuler.lean` is the Euler polynomial of
that spectrum. Everything is derived from existing Library interfaces, the helper
modules `UnramifiedReciprocityBridge`, `CharacterSumEuler` and
`CharacterSumConverse`, and Mathlib, so the module makes no new literature
claim. It proves neither `FullCorrespondenceUnramifiedStatement` nor any
automorphic statement.

Notation: as in `CharacterSumConverse.md`, `deg(w)` is the integer degree
`Weil.Local.localDegreeInt F w` of a Weil element, `Φ` is
`Weil.Local.localGeometricFrobenius F` (of integer degree `1`), and `ϖ` is
`F.canonicalTopologicalData.uniformizerUnit`. From
`Langlands/Representation/Unramified/Eigenvalues.lean`, a spectrum
`s : Unramified.Eigenvalues n` is an unordered list of `n` units of `ℂ` with
multiplicities (`Sym ℂˣ n`). `Eigenvalues.ofTuple z` forgets the order of a
tuple `z : Fin n → ℂˣ`, and every spectrum has this form
(`Eigenvalues.ofTuple_surjective`). `Eigenvalues.eulerPolynomial s` is the
product of `1 - C z * X` over the members `z` of `s`; for a tuple it is
`∏ i, (1 - C (z i) * X)` (`Eigenvalues.eulerPolynomial_ofTuple`). From
`Langlands/Representation/Unramified/PrincipalSeries.lean`,
`Unramified.characterSpectrum F χ` is the spectrum of the uniformizer values
`χ i ϖ` of quasi-characters `χ : Fin n → QuasiCharacter F`, and
`Unramified.characterTuple F z` is the tuple of unramified quasi-characters with
uniformizer values `z i`. `unramifiedCharacterSumClass F c` (from
`CharacterSumConverse`) is the unramified class whose geometric Frobenius lift has
eigenvalues `c i`, namely the character sum of the unramified characters
`w ↦ c_i ^ deg(w)`.

## Unramified classes are unramified character sums

- `exists_eq_unramifiedCharacterSumClass`: if
  `D : WeilDeligneClass.{uF, uP} F r.succPNat` satisfies
  `IsUnramifiedParameterClass F D`, there is `c : Fin (r + 1) → ℂˣ` with
  `D = unramifiedCharacterSumClass F c`. The proof takes a representative `a` of
  `D`. The witness of `IsUnramifiedParameterClass` is a zero-monodromy pair
  equivalent to `a` with trivial inertia action. Hence `a` has zero monodromy
  (`monodromy_eq_zero_of_equiv`) and trivial inertia action
  (`isUnramified_of_equiv`). `a` is Frobenius-semisimple and `Φ` has nonzero
  degree, so `a.representation Φ` is semisimple.
  `exists_basis_apply_eq_smul_of_isSemisimple` from `CharacterSumConverse` gives
  an eigenbasis indexed by `Fin (finrank ℂ a)` with eigenvalues `μ j`. Each
  `μ j` is nonzero, because applying `Φ⁻¹` to `Φ (b j) = μ j • b j` would
  otherwise give `b j = 0`. The rank of `a` is `r + 1`, so the basis is
  reindexed by `Fin (r + 1)`, and `c i` is the unit with value `μ` at the
  corresponding index. `nonempty_equiv_characterSumPair` from
  `CharacterSumConverse` makes `a` equivalent to the character-sum pair of the
  characters `localUnramifiedCharacter F (c i)`.
  `parameterForget_characterSumClass` and `parameterForget_injective` finish the
  proof.

## The class of a spectrum

- `unramifiedSpectrumClass F s` (definition): for
  `s : Unramified.Eigenvalues (r + 1)`, the class
  `unramifiedCharacterSumClass F c` in `WeilDeligneClass.{uF, uP} F r.succPNat`,
  where `c` is an ordering of `s` chosen by `Classical.choose` from
  `Eigenvalues.ofTuple_surjective`. The class does not depend on the chosen
  ordering, by `unramifiedCharacterSumClass_eq_unramifiedSpectrumClass` below.
- `parameterEulerPolynomial_unramifiedSpectrumClass`:
  `parameterEulerPolynomial F (unramifiedSpectrumClass F s) =
  Eigenvalues.eulerPolynomial s`. By
  `parameterEulerPolynomial_unramifiedCharacterSumClass` the left side is
  `∏ i, (1 - C (c i) * X)` for the chosen ordering `c`. Since
  `Eigenvalues.ofTuple c = s`, `Eigenvalues.eulerPolynomial_ofTuple` identifies
  this product with `Eigenvalues.eulerPolynomial s`.
- `unramifiedCharacterSumClass_eq_unramifiedSpectrumClass`: for every tuple
  `c : Fin (r + 1) → ℂˣ`, `unramifiedCharacterSumClass F c =
  unramifiedSpectrumClass F (Eigenvalues.ofTuple c)`. By the previous result
  and `Eigenvalues.eulerPolynomial_ofTuple`, the right side has standard Euler
  polynomial `∏ i, (1 - C (c i) * X)`. `parameterEulerPolynomial_eq_prod_iff`
  from `CharacterSumConverse` then identifies it with the left side.
- `parameterEulerPolynomial_eq_eulerPolynomial_iff`: for `D` of rank `r + 1`
  and a spectrum `s`, `parameterEulerPolynomial F D =
  Eigenvalues.eulerPolynomial s` holds exactly when
  `D = unramifiedSpectrumClass F s`. No unramifiedness hypothesis on `D` is
  needed. Writing `s = Eigenvalues.ofTuple c`, this is
  `parameterEulerPolynomial_eq_prod_iff` combined with the previous result.
- `unramifiedSpectrumClass_injective` and `unramifiedSpectrumClass_inj`: equal
  classes have equal spectra. Equal classes have equal standard Euler
  polynomials, hence `Eigenvalues.eulerPolynomial s =
  Eigenvalues.eulerPolynomial t`. The published
  `Eigenvalues.eulerPolynomial_injective`
  (`Langlands/Representation/Unramified/SphericalSpectrumUniquenessProof.lean`)
  gives `s = t`.
- `unramifiedCharacterSumClass_eq_iff`: two unramified character-sum classes
  `unramifiedCharacterSumClass F c` and `unramifiedCharacterSumClass F c'` are
  equal exactly when `Eigenvalues.ofTuple c = Eigenvalues.ofTuple c'`, that is,
  when the tuples agree up to order. This combines the two previous results.

## Unramified classes and spectra

- `isUnramifiedParameterClass_unramifiedSpectrumClass`: every
  `unramifiedSpectrumClass F s` is an unramified parameter class, by
  `isUnramifiedParameterClass_unramifiedCharacterSumClass`.
- `isUnramifiedParameterClass_iff_exists_unramifiedSpectrumClass`: a class `D`
  of rank `r + 1` is unramified exactly when `D = unramifiedSpectrumClass F s`
  for some spectrum `s`. The forward direction applies
  `exists_eq_unramifiedCharacterSumClass` and then takes
  `s = Eigenvalues.ofTuple c`. By injectivity this `s` is unique.
- `isUnramifiedParameterClass_iff_exists_eulerPolynomial`: a class `D` of rank
  `r + 1` is unramified exactly when `parameterEulerPolynomial F D =
  Eigenvalues.eulerPolynomial s` for some spectrum `s`. This rewrites the
  previous result with `parameterEulerPolynomial_eq_eulerPolynomial_iff`.

## Character-sum parameters

Let `e` be a geometric candidate (`IsGeometricReciprocity F e`).

- `isCharacterSumParameter_iff_eq_unramifiedSpectrumClass`: if every `χ i` is
  unramified, then `IsCharacterSumParameter F e χ D` holds exactly when
  `D = unramifiedSpectrumClass F (Unramified.characterSpectrum F χ)`. By
  `isCharacterSumParameter_iff_parameterEulerPolynomial` and
  `parameterEulerPolynomial_eq_prod_iff`, the left side says
  `D = unramifiedCharacterSumClass F (fun i => χ i ϖ)`. That class is
  `unramifiedSpectrumClass F (Eigenvalues.ofTuple (fun i => χ i ϖ))`, and this
  spectrum is `Unramified.characterSpectrum F χ` by definition.
- `isCharacterSumParameter_unramifiedSpectrumClass`: for unramified `χ i`, the
  class `unramifiedSpectrumClass F (Unramified.characterSpectrum F χ)` is the
  character-sum parameter of `χ`. This is the reverse direction of the previous
  result.
- `isCharacterSumParameter_characterTuple`: for every `z : Fin (r + 1) → ℂˣ`,
  `unramifiedCharacterSumClass F z` is the character-sum parameter of
  `Unramified.characterTuple F z`. These characters are unramified
  (`characterTuple_isUnramified`), and their spectrum is
  `Eigenvalues.ofTuple z` (`characterSpectrum_characterTuple`), so the first
  result and `unramifiedCharacterSumClass_eq_unramifiedSpectrumClass` apply.

The module adds no continuity hypothesis. Semisimplicity of `Φ` comes from the
Frobenius-semisimple condition built into `WeilDeligneClass`.
