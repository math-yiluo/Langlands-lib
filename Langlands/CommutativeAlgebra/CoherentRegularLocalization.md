# Localization of coherence and finite projective dimension

This internal algebraic prerequisite defines `FinitelyPresentedRegularRing R`
as the conjunction of `FiniteFreeSubmoduleCoherent R` and
`FiniteProjectiveDimensionForFinitelyPresentedModules R`.
The first condition requires every finitely generated submodule of every
finite free module `Fin n → R` to be finitely presented.
The second requires every finitely presented `R`-module in the universe of
`R` to have some finite projective-dimension bound, which may depend on the
module. This definition imposes neither Noetherianity nor locality.
It does not identify this condition with Mathlib's Noetherian regular-ring
class.

`finiteFreeSubmoduleCoherent_of_isLocalization` proves that the first
condition holds for any localization algebra `A` of `R` at any submonoid
`S` if it holds for `R`. The universes of `R` and `A` are independent.
For a finitely generated submodule `P` of `A^n`, localize `R^n`
coordinatewise and descend the generators of `P` to a finitely generated
submodule `K` of `R^n`. The coherence hypothesis makes `K` finitely
presented. The actual map from `K` to its localized submodule is a
base-change map, so finite presentation passes to that submodule.
Its equality with `P` gives the required finite presentation.

`hasProjectiveDimensionLE_of_isLocalizedModule` transports a given bound
`n` from `M` to an actual localization model `f : M → N`. Here `M`, `N`,
and `R` lie in the same arbitrary universe, and `N` has compatible `R`
and `Localization S` actions. Mathlib preserves the bound under its
bundled exact localization functor. Uniqueness of localization models
gives an `R`-linear equivalence with `N`; extension of scalars makes it
linear for the specified `Localization S` action. The resulting module
isomorphism transports the bound.

`finiteProjectiveDimensionForFinitelyPresentedModules_localization`
proves permanence of the second condition. For a finitely presented
module `N` over `Localization S`, use
`finitelyPresentedLocalizationModel` to produce a finitely presented
carrier over `R` in the universe quantified over by the condition,
together with its actual localization map to `N`. Obtain a bound for
the carrier and apply the preceding transport result. Coherence is
not needed for this step. The conjunction therefore passes to
localizations in `finitelyPresentedRegularRing_localization`.

The valuation-domain corollaries use
`ValuationFiniteFreePresentation`: arbitrary valuation domains satisfy
both conditions, and hence so do all their localizations. The final
theorem retains the sharper uniform projective-dimension bound at most
one for finitely presented modules over these localizations. It descends
the module and transports the bound one from the valuation-domain
presentation. No submonoid is required to avoid zero, so the
localization conclusions also cover the zero ring.

These results provide localization permanence. Polynomial and smooth
algebra permanence, geometric extension and gluing of line bundles,
and the canonical chosen-fraction-field restriction isomorphism remain
separate obligations.
