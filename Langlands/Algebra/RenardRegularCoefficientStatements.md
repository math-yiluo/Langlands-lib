# Actual regular-factor coefficient comparison statements

Authored by Worker 6. These four proposition definitions are derived internal
infrastructure for the common-coefficient input setting of Renard's F/P duality.
Their governing motivation is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, I.2.1 (printed p.14 /
PDF20), I.2.2–I.2.3 (printed pp.15–18 / PDF21–24), and I.4.2 (printed pp.23–24 /
PDF29–30). Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source does not state these four adapters as separate results. Their
provenance is the published coefficient-recovery and uniqueness construction,
`NondegenerateScalars.module` and `module_eq_of_compatible`, and the precise
`NonUnitalBimoduleTensorScalars.InputCompatible` interface.

`RightRegularCoefficientComparison` states equality of entire `Module k B`
structures: recovering coefficients from the exact original action
`NonUnitalModule.rightRegular B` returns B's supplied coefficient Module.
Here B is an idempotented nonunital ring with coefficient-bilinear
multiplication over a commutative ring k. The nondegeneracy proof is exactly
`NondegenerateTensorFunctor.rightRegular_isNondegenerate hB`.

`FInputCompatibility` retains a supplied original left A-action on B and an
explicit tower `IsScalarTower k A B` relative to B's given coefficients. It
asserts the tensor adapter's `InputCompatible` law with S=A, R=B, X=B, using
the exact right regular action and its named nondegeneracy proof. Thus its
conclusion uses the right-B-recovered coefficients, while its input tower
uses B's given coefficients. No nondegeneracy or idempotentedness for A is
needed by this particular comparison.

`RightActionCoefficientComparison` starts with a supplied original right
A-action on B, a fixing-idempotent nondegeneracy witness, and the explicit
tower `IsScalarTower k Aᵐᵒᵖ B` relative to B's supplied Module. It asserts
that the entire right-A-recovered Module equals that supplied Module. This
comparison needs no coefficient laws for B's own multiplication.

`PInputCompatibility` assumes additionally the scalar-tower half of
coefficient bilinearity for B's multiplication. It installs exactly
`NonUnitalModule.regular B` as the residual left action and asserts
`InputCompatible` with S=B, R=A, X=B, for the right-A-recovered coefficients.
It does not require B to be idempotented or the original right action to
come from an algebra homomorphism.

`RegularCoefficientComparisons` is the conjunction of the universal forms
of these four assertions. The universes of k, A and B vary independently.
The regular actions are selected within the propositions; no alternate
ambient action is silently used. The two Module equalities compare actual
structures on the unchanged additive group, not values for a finite set
of scalars or a replacement carrier.

This file contains statements only. It supplies no proof of the four claims.
They give sufficient coefficient inputs for later actual F/P specializations;
commutation of arbitrary original actions alone supplies none of the input
towers assumed here. In particular this file does not resolve the full-source
coefficient-convention question recorded in
`notes/renard/duality-coefficient-conventions.md`, and does not construct a
tensor-dual evaluation map, an inverse, an isomorphism or naturality.
