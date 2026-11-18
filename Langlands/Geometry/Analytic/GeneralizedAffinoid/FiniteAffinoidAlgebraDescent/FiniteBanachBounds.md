# Controlled finite coefficient changes and bounded algebraic comparisons

This internal finite Banach toolkit proves bounds directly from the supplied
norm-controlled coefficient lifts. Every theorem works over arbitrary normed
coefficient fields, including trivial valuations, without completeness or
ultrametric hypotheses.

`BoundedAlgHom.IsFiniteBanach.exists_coefficient_lifts` gives controlled
coefficient lifts for any fixed finite tuple whose coefficient map is
surjective, provided the original map is already finite Banach. Express
each generator in an original controlled tuple as a finite combination of
the new generators. Substituting these expressions into controlled lifts
gives the new coefficient tuple by a fixed finite matrix. A finite sum of
the row norms, plus one, bounds this matrix. Its product with the original
lift bound gives a positive uniform bound, including when a tuple is empty.
This theorem does not upgrade mere algebraic module finiteness to finite
Banach structure.

`BoundedAlgHom.ofFiniteBanachTriangle` equips an algebraic map `h : B → C`
with a bound when it lies over bounded maps `f : A → B` and `g : A → C`
and `f` is finite Banach. Write each `y` using a controlled coefficient
lift in a finite tuple `b`. Its image is the finite sum of `g(c i) * h(b i)`.
The bound for `g`, the controlled coefficient bound, and the finite sum of
`‖h(b i)‖` plus one give an explicit positive bound for `h`. The algebraic
map and the entire coefficient triangle are retained exactly.

`BoundedAlgEquiv.ofFiniteBanachTriangle` applies this construction in both
directions to an algebraic equivalence over the fixed base when both
structural maps are supplied finite Banach. The inverse coefficient triangle
follows by cancelling the original algebraic equivalence. The result retains
the original entire algebraic equivalence.

The source context is the boundedness argument for maps from finite Banach
modules in Berkovich 1990, Proposition 2.1.9, printed p.24 / PDF p.38,
registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
The implemented formulas are elementary derived versions for the Library's
actual coefficient-map norm convention. The two-sided equivalence requires
finite Banach structure on both targets; it does not infer the inverse bound
from algebraic finiteness of one target. These bounds support the unrestricted
original base-change comparisons needed for effective affinoid descent.
