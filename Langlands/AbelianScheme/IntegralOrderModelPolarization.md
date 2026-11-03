# Geometric polarizations on the actual integral order model

This internal application works over an arbitrary `S : Scheme.{u}`, with an
actual abelian scheme `A`, a rational algebra action `α`, and a supplied
`IntegralOrderModel` for the restriction of `α` to an integral subalgebra `O`.
No lattice condition on `O` is needed for this application. The model already
contains an actual abelian scheme `M.B`, two integral maps, their exact
inverse-multiple identities, and positivity of their common integer `N`.
The constructed map is the published `IntegralOrderModel.dualPullbackHom`,
namely the composite of the actual reverse map `M.B → A`, the supplied
polarization on `A`, and the actual dual of that same reverse map.

The pullback-tensor preservation, composition, unit, associativity, left-unitor
comparison, symmetry, Picard-zero pullback, Mumford Picard-zero, universal
base-change, selected dual representability and geometry, and inverse
line-bundle evaluation prerequisites remain explicit. The additional dual
additivity assumptions concern only endomorphisms of `A` and `M.B`. The
dual abelian schemes and all dual maps are those constructed from these
selected data; no replacement dual or compatibility equation is assumed.

`dualPullback_isPolarization` takes invertibility of `N` in the global sections
of `S` and a proof that the supplied map on `A` is a relative polarization.
The published exact inverse-multiple criterion proves that both model maps
are finite etale isogenies. Applying the actual dual inverse-data construction
and the same criterion proves that both actual dual maps are finite etale
isogenies. In particular, the reverse map and its actual dual satisfy the
premises of `isPolarization_integralDualPullbackHom`. That theorem proves
`IsPolarization` for the unchanged model pullback: its composite is an isogeny,
and on every algebraically closed geometric fibre it has an ample Mumford
presentation after a field extension. This argument supplies the geometric
polarization property rather than merely rational involution compatibility.

`dualPullback_isPolarization_overField` removes the global-unit premise when
`S` is supplied with a morphism to the spectrum of a characteristic-zero
field `K : Type u`. The model integer is nonzero, so its image in `K` is a
unit. The composite from `K` through the canonical global sections of
`Spec K` to the global sections of `S` sends that unit to the integer `N`.
The preceding theorem then proves the same polarization property.

`polarizationOverField` bundles the actual model pullback with that proof.
Its value is literally the pre-existing `dualPullbackHom`; the construction
retains the model maps and their common integer and makes no new choice of
rational representatives.

The provenance is internal: this module composes the published integral-model
comparison, exact inverse and actual-dual isogeny criteria, and geometric
polarization transport. It assumes the supplied model and the displayed
conditional dual infrastructure. It does not prove existence of the model,
produce a global relatively ample bundle, or prove the division-case CM
representability statement.
