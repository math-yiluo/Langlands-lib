# Actual small-etale associated coefficient sheaves

Author: Worker 57.

The geometric input is an actual Mathlib scheme `X` and an action of a group
`G` on an actual object of `X.Etale`. Thus the cover, all deck maps, their
composition laws and their compatibility with the morphism to `X` are actual
scheme-theoretic data. The code does not accept an output coefficient sheaf.

`etaleAssociatedFunctor` specializes the accompanying invariant-sheaf
construction to `Scheme.smallEtaleTopology X`, starting with the actual
constant sheaf of an `R`-module representation. It constructs its value on
equivariant module maps as well. `etaleAssociatedSystem` transports an
existing inverse diagram of such representations to a diagram of actual
etale sheaves; transitions are the functorial images of the coefficient maps.
The scheme, ring, coefficient carriers and group use universe `u`. The
small-etale category itself has its existing larger object universe, which
does not force enlargement of coefficient carriers.

`IsFiniteGeometricTorsor` records the precise additional geometric condition:
the group is finite, the etale morphism is finite and surjective, and the
action is free and transitive on the lifts of each geometric point over any
separably closed field in the scheme universe. In the displayed equation
`a ≫ deck(g) = b`, both lifts have the same image in `X`. Existence and
uniqueness quantify the actual deck element. This is not a sectionwise
claim that would incorrectly require a globally constant deck element on
disconnected test schemes.

The sheaf construction itself does not require this predicate. A theorem
using the predicate to prove the expected pullback trivialization remains
an explicit obligation; neither the predicate nor an arbitrary cover action
is asserted to provide that theorem already. No canonical Shimura scheme,
level-cover torsor, algebraic lattice, lisse comparison, or adic coefficient
comparison is claimed by this module.

The original source is Harris, *Galois properties of cohomological automorphic
forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), printed page 311 (PDF
page 13), read by Worker 57. The paragraph following (4.8) descends the
constant étale sheaf of a deeper level to a lisse sheaf on the lower level;
the paragraph preceding Proposition 4.10 forms the inverse system of these
finite coefficient sheaves. The explicit geometric
torsor predicate and the categorical invariant presentation are derived
implementation choices for that step. Source registration
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`;
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Formal dependencies: the accompanying `Coefficients.Associated`, Mathlib
`AlgebraicGeometry.Sites.EtalePoint` and `AlgebraicGeometry.Morphisms.Finite`,
commit `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0. Mathlib
supplies the finite-product structure on the actual etale category, site
localization, module-sheaf limits and constant-sheaf construction.
