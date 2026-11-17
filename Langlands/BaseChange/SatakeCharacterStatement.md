# The Satake parametrization of spherical characters

Module `Langlands.BaseChange.SatakeCharacterStatement`.
`Langlands.BaseChange.SatakeCharacterStatement.{u}` is a proposition-valued definition
(statement 6 of Task 7424). It states an unproved obligation; it is neither proved nor
assumed in this module.

## Statement

The module repeats, as local instances, the canonical topology, valuative relation and
local-field structure of `F.Carrier`, and the canonical topology, topological-group,
Hausdorff, Borel measurable and Borel space structures on `GL_n(F)` used by
`Langlands/Representation/Unramified/HeckeOperators.lean`, so that
`SphericalHeckeAlgebra F r` is the Library's spherical Hecke algebra.

For every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{u} p` and every `r : ℕ`
(the group is `GL_{r+1}(F)`):

- (a) for every Satake parameter `s : Eigenvalues (r + 1)` (an unordered `(r+1)`-tuple of
  nonzero complex numbers) there is a complex algebra homomorphism
  `ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ` with `IsSatakeCharacter F r s ω`, that is,
  `ω (standardHeckeElement F r i) = standardHeckeScalar F s i = q^{i(r+1-i)/2} e_i(s)` for
  every `i : Fin (r + 2)`;
- (b) every `f : SphericalHeckeAlgebra F r` such that `ω f = 0` for every `s` and every `ω`
  with `IsSatakeCharacter F r s ω` is `0`.

By `IsSatakeCharacter.unique` (module `Langlands.BaseChange.UnramifiedHecke`) the
character in (a) is unique; (a) and (b) together say that `f ↦ (s ↦ ω_s(f))` is an
injective map from the spherical Hecke algebra to functions on the Satake parameters.

## Source

This is the content of the Satake isomorphism used by Henniart-Lemaire (2011), §I.3.1,
printed pp. 24-25 (source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, PDF page =
printed page + 8), where it is cited as their reference [57] (Laumon, *Cohomology of
Drinfeld modular varieties I*, 1996, 4.1); see also Gross, *On the Satake isomorphism*
(1998), source ID `gross-1998-satake-isomorphism`, Proposition 3.6 and (3.14).

Derivation (provenance: derived from these sources). The Satake transform
`S_F : H_F → ℂ[X_1^{±1}, …, X_n^{±1}]^{S_n}` (`n = r + 1`) is an algebra isomorphism,
and `S_F(standardHeckeElement F r i) = q^{i(n-i)/2} e_i(X_1, …, X_n)` (Gross (3.14)).
A symmetric Laurent polynomial can be evaluated at an unordered tuple `s` of nonzero
numbers, so `φ ↦ S_F(φ)(s)` is an algebra character with the values required in (a). If
`S_F(f)(s) = 0` for every `s`, the Laurent polynomial `S_F(f)` vanishes on `(ℂˣ)^n`, hence
is zero, and `f = 0` by injectivity of `S_F`; with the uniqueness of the character at
`s`, this gives (b). The statement uses only injectivity of `S_F` and its values on the
standard elements, not its surjectivity (which statement 7,
`Langlands.BaseChange.UnramifiedBaseChangeHomStatement`, needs).

HL work over local fields of any characteristic; this statement is for the Library's
`PadicField`s, the setting of its spherical Hecke algebra. Whether the Satake transform
is normalized with `X^ν` or `X^{-ν}` does not matter here: the other normalization replaces
`s` by its entrywise inverse, a bijection of the parameters.
