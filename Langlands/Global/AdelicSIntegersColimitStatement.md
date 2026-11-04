# The fields as colimits of their actual integer rings

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed p.6, Remark 3.5, uses the outside-S integer rings as a
filtered system with colimit the global field. These targets express
that assertion for the actual arithmetic rings, as commutative algebras
over any fixed original outside-S integer ring.

`CurvePlaceSIntegersColimitStatement` quantifies a function field F over
a perfect field k, with the compatible k- and rational-function-field
algebra structures explicit. For every initial finite S, it asserts
that every element of F belongs to a stage indexed by a finite T
containing S, and that the literal field-valued cocone
`curvePlaceSIntegersOverCocone k F S` is a categorical colimit.
`FunctionField k F` means that F is finite dimensional over `RatFunc k`.
No separability of that extension, nonempty S, or finiteness of k is
assumed.

`NumberFieldSIntegersColimitStatement` asserts the analogous exhaustion
of an arbitrary number field K by Mathlib's actual S-integer
subalgebras, and the colimit property of
`numberFieldSIntegersOverCocone K S`. The index contains finite places.
There is no integrality condition at infinite places in these integer
rings.

The final proposition `AdelicSIntegersColimitStatement` is the
conjunction of these two universally quantified assertions in an
arbitrary common universe. Both cocones use the original field and the
literal integer inclusions. Their algebra structures are the original
inclusions of the fixed initial integer ring; the target is not an
unidentified isomorphic field.

The formulation is derived from Conrad's global-field application.
It explicitly extends the function-field branch to arbitrary perfect
constant fields: the published finite-poles theorem has this scope,
and the colimit argument only uses that finite-poles exhaustion and
compatibility of the integer inclusions. Finite constant fields,
including the actual global function fields of positive characteristic,
are included. The number-field exhaustion uses finiteness of the
nonintegral support of an element of a Dedekind domain's fraction field.
Enlarging the finite support by S preserves membership.

These are algebraic colimit targets, with no topology asserted.
Scheme-limit comparison, existence of spreads, generic-fiber point
identification, independence of arbitrary spreads, and the formal
proof of these propositions remain separate obligations.
