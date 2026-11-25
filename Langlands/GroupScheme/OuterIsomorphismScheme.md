# Supplied outer-isomorphism quotients and their actual fibres

This internal interface concerns a supplied `GroupIsomorphismScheme G H`
and an actual automorphic action of a group scheme `A` on `G`, over an
arbitrary base. The isomorphism scheme has the canonical left action
by inverse precomposition.

`OuterIsomorphismScheme` supplies an actual relative outer-class scheme
and class morphism from that isomorphism scheme. The underlying class
morphism is flat, surjective and quasi-compact. Its class is invariant
under the canonical action on every relative test. Moreover, each pair
of points with the same class differs by a unique point of `A`, on every
test. These are hypotheses on supplied geometry, not an assertion that
such geometry exists.

For an actual integral outer section `s`, `fibre` is the scheme pullback
of the class morphism along `s`; `fibreProjection` is its morphism to the
isomorphism scheme. `fibreModObj` restricts the canonical action using
`ActionFibre`. Its structure morphism is flat, surjective and
quasi-compact, and `fibreShear` proves that its categorical shear is an
isomorphism, from the supplied unique-difference condition.

`fibreLocalIso` restricts the universal isomorphism to this fibre.
`fibreLocalIso_smul` proves the same inverse-precomposition equation on
every relative test, using equivariance of the fibre projection and the
evaluation equation for the universal isomorphism scheme action.
`fibrePoint` lifts any specified isomorphism point with this class;
`fibreLocalIso_refine_fibrePoint` proves equality of its entire natural
family with the original one.

`FiniteGenericOuterClass` supplies a finite scheme over the base with a
morphism to the outer scheme and a point mapping to the outer class of
one specified isomorphism point. No finiteness of the whole isomorphism
scheme or outer scheme is required. Over a valuation domain and its
specified fraction field, `integralClass` extends that finite-scheme
point by `finiteGenericSection` and then maps it to the outer scheme.
`integralClass_generic` retains the exact outer class. The constructed
`genericFibrePoint` belongs to that integral fibre, and
`genericFibrePoint_localIso` retains the exact original natural family.

The module consists of internal constructions from the imported
representation, action-fibre and finite-section interfaces. Existence of
the isomorphism scheme, outer quotient and finite component remains a
separate obligation, as does the choice of the acting group as the
relative full-centre adjoint quotient. No such existence theorem is
claimed here.
