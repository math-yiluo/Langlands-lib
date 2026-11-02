# Descent of finitely presented modules through localization

This is an internal construction using Mathlib's finite-presentation and
localized-module APIs. Let `R` be a commutative ring, let `S` be a submonoid
of `R`, and let `N` be a finitely presented module over `Localization S`.
Give `N` an `R`-module structure compatible with its localized-ring action
through `IsScalarTower R (Localization S) N`. The construction produces
a finitely presented `R`-module whose localization is the specified `N`.
No coherence, locality, domain or Noetherian hypothesis is imposed.

`FinitelyPresentedLocalizationModel R S N` records a natural number
`rank`, a finitely generated relation submodule of `Fin rank → R`, an
actual `R`-linear map from the quotient by these relations to `N`, and
an `IsLocalizedModule S` witness for that map. Its `Carrier` is this
quotient, in the universe of `R`; `N` may lie in an independent universe.
The `finitePresentation` and `localizedModule` instances expose the two
properties. If the compatible localized-ring action on `N` is available,
`localizationEquiv` is an actual `Localization S`-linear equivalence
from `LocalizedModule S Carrier` to `N`.

`nonempty_finitelyPresentedLocalizationModel` proves that such a model
exists for every finitely presented `N`.
`finitelyPresentedLocalizationModel` selects one noncomputably.
This is an existence and choice construction; it asserts neither
canonical choices nor uniqueness of the descended module.

The supporting theorem `exists_fg_submodule_localized'_eq` allows
independent universes for a commutative localized ring `A`, the original
`R`-module `M`, and its localized-module model `N`. For an `R`-linear
localization map `f : M →ₗ[R] N`, every finitely generated `A`-submodule
`P` of `N` is `K.localized' A S f` for some finitely generated
`R`-submodule `K` of `M`.

The proof first chooses finitely many generators of `P` and numerator
and denominator representatives for them. It takes `K` to be the
`R`-span of the numerators. A numerator maps to its generator multiplied
by its denominator, giving one inclusion of localized submodules.
The chosen fraction representations give the reverse inclusion.

For finite-presentation descent, Mathlib supplies an isomorphism between
`N` and a quotient of a finite free localized module by finitely
generated relations. Coordinatewise localization identifies that free
module with the localization of `Fin rank → R`. The preceding
submodule theorem descends its relation submodule. Mathlib's quotient
localization map and the quotient isomorphism then give the recorded
localization map to `N`. The finitely generated relations imply that
the descended quotient is finitely presented.
The equivalence `localizationEquiv` uses uniqueness of localized-module
models and extends the resulting `R`-linear equivalence to the compatible
localized-ring actions.

This algebraic prerequisite makes no claim about projective dimension,
Picard groups, smooth valuation algebras or extension of line bundles on
schemes.
