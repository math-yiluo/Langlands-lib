# Whittaker type from scalar multiplicity

Author: Worker 288.

The theorem `Langlands.RankinSelberg.whittakerTypeFromMultiplicity.{uF,uV}`
proves the closed published proposition
`Langlands.RankinSelberg.WhittakerTypeFromMultiplicityStatement.{uF,uV}`
from [WhittakerTypeFromMultiplicityStatement](WhittakerTypeFromMultiplicityStatement.md).
This is an internal algebraic consequence of the existing representation and
Whittaker-functional definitions, with Mathlib supplying the general module
lemmas. No analytic theorem is invoked.

The field universe `uF` and representation-carrier universe `uV` remain
independent. The result quantifies over every field `F` with a topology, every
positive rank `n + 1`, and every character
`θ : upperUnipotent (n + 1) F →* ℂˣ`. It assumes irreducibility and admissibility
of `π` and a functional `ℓ` in the full `θ`-equivariant functional submodule
such that `ℓ.val ≠ 0` and every functional in that submodule is `c • ℓ` for some
complex scalar `c`. It assumes neither finite-dimensionality of the carrier
nor finite generation over the group algebra.

The proof has two algebraic steps. First,
`Representation.irreducible_iff_isSimpleModule_asModule` turns irreducibility
into simplicity of `π.asModule` over
`MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F)`. Mathlib's simple-module
`IsNoetherian` instance and `IsNoetherian.finite` then provide finite generation
over that group algebra. This does not assert finite dimension over ℂ.

Second, `LinearMap.toSpanSingleton ℂ _ ℓ` is the complex-linear map
`c ↦ c • ℓ` into the entire functional submodule. Nonvanishing of `ℓ.val`
implies nonvanishing of the bundled `ℓ`, so `smul_left_injective` proves that
map injective. The explicit scalar-multiple hypothesis proves it surjective.
`LinearEquiv.ofBijective` and its inverse therefore give the required linear
equivalence from the functional space to ℂ. Together with the supplied
admissibility and derived finite generation, this is exactly
`Langlands.RankinSelberg.IsOfWhittakerType n θ π`.

This theorem packages supplied algebraic hypotheses. It does not establish
existence of a nonzero Whittaker functional, multiplicity one, or genericity of
square-integrable representations. Those inputs must be proved separately in
applications. No continuity, nontriviality, or standard-character condition is
added to the arbitrary character `θ`.
