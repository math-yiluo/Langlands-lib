# Regular-function smoothness under actual affine base change

This internal derived construction concerns an affine scheme `X` over a
commutative ring `C`, a commutative `C`-algebra `D`, and a commutative value
ring `A` with compatible `C`- and `D`-algebra structures. All algebraic
objects lie in one arbitrary universe. A specified ring map `c : A → B`
has values in a real normed commutative algebra in an independent universe.
Parameter spaces are arbitrary real charted spaces with the stated model
with corners; no smooth manifold instance on them is assumed.

`contMDiff_ringPoint_baseChange_iff` proves that the existing actual
pullback-adjunction equivalence `ringPointBaseChangeEquiv` preserves and
reflects the condition that every global regular-function value, after `c`,
is infinitely real differentiable. The tests on the base change range over
all its global functions, including the extended scalar coefficients.
`coefficientSmoothBaseChangeFamilyEquiv` restricts the same actual point
equivalence and its inverse to these subtypes of parameter families.

The implemented proof first treats algebra points. Evaluation of a pure
tensor is the product of a fixed scalar value and an original evaluation.
Tensor induction and smoothness of multiplication and addition prove one
direction; evaluation at `1 ⊗ a` proves the other. An actual affine spectrum
presentation preserves and reflects all such tests, by the inverse
isomorphisms of the coordinate algebras and naturality of point evaluation.
Finally, the existing inverse-coordinate formula for the original
pullback-adjunction equivalence identifies its tensor coordinates with the
algebra scalar-extension map. These are identities of the original relative
scheme points, rather than a choice of a different carrier.

The arbitrary topology on `A` is used only to invoke the published affine
presentation and inverse-coordinate formulas. No topological ring hypothesis
on `A` or continuity assumption on `c` is needed. Smoothness is tested after
`c` in `B`. The construction supplies no analytic manifold instance on the
point spaces and proves no Lie group, differential growth, measure or
reduction theorem. It is based on the existing actual affine-base-change
constructions and Mathlib's tensor induction and real smooth operations,
without an external source assertion.
