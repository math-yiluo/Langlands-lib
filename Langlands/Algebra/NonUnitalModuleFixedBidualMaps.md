# Fixed-space bidual comparison maps

This internal construction supports Renard's I.5.1 proposition, printed p.26 /
PDF32 of the French edition dated 9 July 2026. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The corrected converse in the registered 2010 errata,
`renard-2010-corrections-complements`, SHA-256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF2, passes through the
ordinary algebraic bidual of each fixed space; the 2026 proof incorporates that
argument. The named maps here are implementation infrastructure, not separately
named source assertions.

The algebra A and module carrier M have independent universes. A is a possibly
nonunital complex algebra with the published idempotented-ring hypotheses.
M retains its original additive action and nondegeneracy witness. There is no
ambient supplied complex module on M and no finite-dimensionality hypothesis.

`FixedBidual hA hM e` is precisely the actual idempotent-fixed subgroup of
`NonUnitalModuleDual.Bidual hA hM`, using exactly the published original
A-action `bidualAction`. Its coefficients are exactly
`NonUnitalModuleCorner.complexModule hA (bidual_isNondegenerate hA hM) e`.
`OrdinaryBidual hA hM e` is the ordinary algebraic complex bidual of the
actual fixed subgroup of M, with precisely its published recovered scalars.

`canonicalBidualModule_eq` identifies the entire recovered module on the actual
bidual with its inherited pointwise complex module. Its proof transports the
published scalar tower through the double opposite and uses the uniqueness of
recovered scalars. This justifies subsequent linearity for the exact source
coefficients.

`extendToDual` includes the published projection-extension map into the actual
first dual, with its recovered coefficients. `restrictFromDual` restricts any
actual dual functional to the original fixed subgroup. On a functional ell and
a vector m, extension has value ell(e m); restriction has value phi(x).

`toOrdinaryBidual` precomposes an actual fixed bidual functional with
`extendToDual`. In the other direction, `ordinaryToFull` precomposes an
ordinary bidual functional with `restrictFromDual`. The same double-opposite
idempotent fixes the entire resulting functional, so it belongs to the actual
nondegenerate bidual and is fixed by the original e. `fromOrdinaryBidual`
retains both of these subtype witnesses. The application and whole-functional
formulas in Lean describe these exact maps.

This unit supplies maps and their intrinsic well-definedness and linearity
computations. Complete unapplied signature checks retain both independent
universes, all original algebra and module instances, both nondegeneracy
witnesses, and the exact canonical fixed-space coefficient structures. The unit
does not assert their inverse equations, a canonical
evaluation square, finite-dimensional reflexivity, admissibility, or simplicity.
Those mathematical comparisons remain separate statement and proof obligations.
