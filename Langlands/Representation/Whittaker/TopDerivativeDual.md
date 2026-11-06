# Full Whittaker functionals and the dual of the top derivative

Author: Worker 1732. Derived construction.

For an arbitrary prime, actual finite p-adic extension `F`, compatible
topological realization `T`, allowed continuous nontrivial unitary additive
character `ψ`, and actual smooth complex representation `π` of `GL_n(F)`,
`functionalsTopDerivativeDualEquiv` identifies the entire algebraic space of
functionals for the all-rank entrywise upper-unipotent character with the
algebraic dual of the entire actual top derivative. The field universe `uF`
and representation-carrier universe `uV` are independent.

The construction first applies the published `functionalsLocalizationDualEquiv`
to the actual quotient by the relations `π(u)v - θ(u)v`. The published natural
isomorphism `TopLocalization.topLocalizationIso` identifies that quotient with
`topDerivative`. The latter includes the group-rank transport from `n - n` to
zero. Equality induction supplies the underlying linear equivalence removing
this transport, without changing the derivative vector space. Pullback along
the inverse of this composite equivalence identifies the two algebraic duals.
These are actual mutually inverse complex-linear maps, not dimension
comparisons. No line or basis is chosen.

`hasFunctional_iff_nontrivial` is the elementary algebraic observation that
existence of a functional whose underlying linear map is nonzero is equivalent
to nontriviality of its entire functional submodule. This helper applies to
arbitrary commutative coefficient rings and groups. The all-rank
`hasFunctional_iff_nontrivial_topDerivative` then follows from the constructed
equivalence and the nontriviality criterion for an algebraic vector-space dual
over the complex numbers.

At rank zero the entrywise character is trivial and the derivative is the
identity, so the construction retains the full dual of the original carrier.
At positive rank the published equality of the entrywise and standard
characters gives `glFunctionalsTopDerivativeDualEquiv` and
`hasStandardFunctional_iff_nontrivial_topDerivative`. Rank one is included.
No irreducibility, admissibility, finite length, finite dimension,
unitarizability or classification hypothesis is imposed. No continuity is
required of a functional or a representation-module map.

The private nonvanishing helpers in Worker 1732's generic segment exhaustion
and socle genericity proofs supplied the implementation pattern. This public
construction retains the full functional space, includes rank zero, and uses
only the published `Derivative.TopLocalizationComparison` and
`Whittaker.LocalizationDual` modules and their imports. The implementation does
not import those two classification proofs. Its provenance is the internal
composition of published quotient and linear-equivalence constructions,
together with elementary dual-space linear algebra; it asserts no new external
literature result. It proves neither higher-Speh nongenericity nor unitary
exhaustion, and supplies no finite-product assertion by itself.
