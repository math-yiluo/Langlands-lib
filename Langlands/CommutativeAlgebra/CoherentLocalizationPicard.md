# Conditional Picard vanishing for coherent local rings

This internal algebraic derivation combines finite-presentation descent
through localization with the stable-freeness result under the explicit
`FiniteFreeSubmoduleCoherent` condition.

`FiniteProjectiveDimensionForFinitelyPresentedModules R` says that every
finitely presented `R`-module in the universe of `R` has a finite
projective-dimension bound. The bound may depend on the module.
Projective dimension is Mathlib's `HasProjectiveDimensionLE` for the
corresponding object of `ModuleCat R`.

The two theorems assume that `R` is a commutative local ring, that
`FiniteFreeSubmoduleCoherent R` holds, and that the preceding
finite-projective-dimension condition holds. The coherence condition
requires every finitely generated submodule of every finite free
`R`-module `Fin n → R` to be finitely presented.
For every submonoid `S` of `R`,
`free_invertible_localization_of_finitelyPresented_finite_projectiveDimension`
proves that every invertible module over `Localization S` is free.
The module may be in an independent universe.
`subsingleton_pic_localization_of_finitelyPresented_finite_projectiveDimension`
then proves that `CommRing.Pic (Localization S)` is a subsingleton.

An invertible module is finite and projective, so Mathlib gives its
finite presentation over the localized ring. Restriction of scalars
gives a compatible `R`-module action. The chosen
`finitelyPresentedLocalizationModel` descends it to a finitely
presented module in the universe of `R`, with an actual localization
map to the original invertible module. The hypothesis supplies a
finite projective-dimension bound for that descended module.
The imported stable-freeness theorem applies to this localization map,
using projectivity of the invertible localized module. Mathlib's
stable-free invertible-module theorem gives freeness. Finally,
Mathlib identifies triviality of the Picard group with freeness of
all invertible modules.

No Noetherian hypothesis is imposed. The coherence and
finite-projective-dimension conditions are hypotheses, and the file
does not prove them for smooth algebras over valuation rings. It
asserts no scheme-level line-bundle extension or two-axis extension
result.
