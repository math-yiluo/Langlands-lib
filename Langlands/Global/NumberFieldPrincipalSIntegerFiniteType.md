# Actual cofinal number-field integer levels of finite type

This construction works with an arbitrary number field `K` in universe `u`,
its original ring of integers, its actual finite places and the literal
`Set.integer` subalgebras of `K`. It constructs cofinal principal exceptional
sets whose outside-set integer rings are of finite type over `ℤ`.

`numberFieldPrincipalExceptional K t` is the finite support of the inverse
of the original integral element `t`. If `t` is nonzero, membership of a place
is exactly membership of `t` in that place's height-one prime ideal. This follows
from multiplicativity of its actual valuation, positivity on nonzero elements,
and the valuation test for membership in the prime.

`numberFieldPrincipalSIntegerEquiv K t ht` is the existing actual away
localization inside `K`, identified with this exact outside-set integer ring.
The valuation membership criterion proves equality of the two actual
subalgebras, and `Subalgebra.equivOfEq` supplies the comparison. It preserves the original integer
coefficients and every element of `K`; its coercion identity is proved.
The scoped `NumberFieldPrincipalSIntegers.finiteType` instance uses finite
presentation of localization away from `t`, then finite type of the original
ring of integers over `ℤ`. Thus this is finite type of the actual integer ring,
not of an auxiliary isomorphic ring without a supplied comparison.

For every finite `S`, choose one nonzero element in each of its actual prime
ideals and multiply them. The product is nonzero, and it belongs to every prime
in `S`. Consequently its principal exceptional set contains `S`. This includes
the empty set: the empty product is one. The definitions
`numberFieldPrincipalDenominator` and `numberFieldPrincipalLevelAbove` retain
this witness and choose an actual index in `AdelicLevelIndexAbove S`.
The instance `numberFieldPrincipalLevelAbove_finiteType` supplies finite type
over `ℤ` of its literal outside-set ring.

The content is an internal arithmetic prerequisite for the model enlargement
in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Remark 3.5 on printed p.6 and the proof of Theorem 4.5 on
printed pp.12–13. It is derived from the already implemented Dedekind
localization comparison and the pinned Mathlib valuation and localization
constructions. It asserts finite type only for the displayed cofinal principal
levels. It does not assert finite type for every initial exceptional set,
compatible model existence, Lang–Weil, or adelic openness.
