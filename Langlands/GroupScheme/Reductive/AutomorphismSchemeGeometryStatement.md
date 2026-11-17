# Relative automorphism schemes and their outer quotient geometry

Worker 812.

`ReductiveAutomorphismSchemeGeometryStatement.{u}` states a selected geometric
part of Brian Conrad, *Reductive group schemes* (2014), Theorem 7.1.9(1),
printed/PDF pp.245–247. The registered source is
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Those three original pages were read in full. No project erratum for this
source was found.

For every scheme `S` and reductive `S`-group `G`, the statement asks for an
actual `GroupIsomorphismScheme G G` whose structure morphism is smooth and
separated. Its universal family classifies natural automorphisms on every
relative scheme test; `LocalGroupIso.baseChangeIsoEquiv` identifies these with
actual automorphisms of the pulled-back group. Tests need not be affine,
connected, reduced, or field-valued.

For every independently supplied reductive full-centre quotient
`q : G ⟶ A` with `hq : IsRelativeAdjointQuotient q`, it further asks for
`O : OuterIsomorphismScheme I hq.innerAction`. This existing interface
requires an actual class scheme and a class morphism that is flat,
surjective, and quasi-compact. The morphism is invariant for the canonical
inverse-precomposition action. Every equal-class pair of points on every
test differs by exactly one `A`-point on that same test. This is the
scheme-level torsor meaning of the inner-orbit quotient; it makes no
assumption that an `A`-point lifts globally to `G`.

The additional geometry says that the class scheme is separated and étale
over `S`, and that the class morphism is affine. The displayed map from
`A.X` to `I.parameter` is a closed immersion. Its classifying family is
the constant identity family, twisted by the canonical inner action at
the universal `A`-point. Thus it sends `a` to its inner automorphism,
without the inverse used in the action on the isomorphism parameter.

The last clause expresses étale local constancy using actual schemes.
There is an étale covering family of `S`; over every member `U`, the
pullback of the class scheme is isomorphic in `Over U` to the disjoint
union of copies of `U` indexed by a type `D : Type u`. No finiteness or
nonemptiness condition is imposed on `D`, and it may depend on the member
of the cover. In particular, the whole outer scheme is not asserted to
be finite or quasi-compact.

This is a derived formulation of the geometry in Theorem 7.1.9(1), rather
than the entire numbered theorem. The represented automorphism functor
determines its group structure, but no separately chosen group structure
on the parameter or outer parameter is part of this interface. The
full-centre quotient is supplied independently, and the statement retains
its unique quotient action. Affineness of the class morphism follows in
the source from its torsor structure under the affine adjoint group, by
effective descent of affine morphisms (p.246). The finite-component
assertion over a normal locally noetherian base and parts (2)–(3) of the
theorem are outside the statement. The original assumes `S` nonempty;
the extension here to the empty scheme is the trivial empty-base case.

This module defines an unproved proposition. Establishing the actual
all-test pinned automorphism decomposition and its effective descent is
the substantial general prerequisite. Neither a base-point classification
nor representability alone supplies the quotient geometry above.
