# Endomorphism and adelic algebra compatibility of actual Tate base change

This module proves that the actual rational Tate pullback comparison
commutes with rational homomorphisms and with the constructed algebra
actions. It bundles the comparison as a linear equivalence over the
full and away PEL tensor algebras.

## Provenance

The construction is derived from the actual pullback maps in
`AbelianScheme.RationalBaseChange`, the rational Tate equivalence in
`Tate.RationalBaseChange`, and the algebra actions in
`Tate.RationalScalars` and `Tate.AwayRationalScalars`.
No arbitrary isomorphism of Tate modules or endomorphism algebras is
an input.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed p.18 / PDF p.26, defines rational Tate modules
and invertible actual rational homomorphisms. Section III.1, printed
pp.91–92 / PDF pp.99–100, uses actual rational endomorphism actions and
full and away adelic module isomorphisms in its pointed PEL problems.
These conventions motivate this derived compatibility construction.
The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

## Actual rational homomorphisms

All declarations are in `Langlands.AbelianScheme.Tate`. Fix a base
morphism `b : S' ⟶ S`, an abelian scheme `A/S`, and a test scheme `T/S'`.
The existing `rationalBaseChange b A T P` maps the rational Tate module
of the actual pullback of `A`, evaluated on `T`, to that of `A`, evaluated
on the composite test scheme `(Over.map b).obj T`. Both sides retain the
same predicate `P` on positive torsion orders.

`rationalBaseChange_homMap` says that this comparison carries the Tate
map of the actual pullback of `f : Hom0 A B` to the original Tate map of
`f`. The proof inducts on the tensor expression for the rational
homomorphism. On `q ⊗ f` it uses the rational scalar law and the existing
naturality for actual integral homomorphisms. Additivity handles sums
and zero. `rationalBaseChange_iso` specializes this square to invertible
rational homomorphisms, using their actual pullback isomorphisms.

`rationalBaseChange_endAction` specializes to an endomorphism and
identifies its pullback via the constructed rational algebra map
`AbelianScheme.rationalBaseChangeEnd b A`. For an algebra map
`i : D →ₐ[ℚ] End0 A`, the action over `S'` is explicitly the composite
of `i` with that pullback algebra map. The lemma
`rationalBaseChange_algebraAction` proves compatibility with this
specific action.

## Full and away tensor algebra actions

`rationalBaseChange_finiteAdeleAction` specializes the previously proved
full scalar law to abelian schemes. The full module structures at both
ends use exactly the same hypothesis
`h : Global.RationalProfiniteIntegerAdeleComparison`.

`rationalBaseChange_finiteAdeleAlgebraAction` proves compatibility with
`D ⊗[ℚ] Global.FiniteAdeles ℚ`. On a pure tensor `d ⊗ a`, the action is
the rational endomorphism action of `i(d)` after scalar multiplication
by `a`. The two already proved compatibilities handle these in order;
additivity and tensor induction handle arbitrary tensors.
`finiteAdeleAlgebraBaseChange` bundles the original rational bijection
with this scalar law. Its application and inverse-application lemmas
identify both maps with the original rational equivalence and its
inverse.

The `primeToFiniteAdele` declarations repeat this construction for
exactly the orders coprime to `m`. Both ends use the same coupled
hypothesis `hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m`.
The resulting equivalence is linear over
`D ⊗[ℚ] Global.PrimeToFiniteAdeles m`, and again has precisely the
underlying rational base-change map and inverse.

`finiteAdeleAlgebraBaseChange_restrictAway` states the full-to-away
square on underlying vectors. It follows from the previously proved
rational restriction square because the bundled maps retain the same
functions. This lemma does not assert linearity of the restriction map
over one unchanged scalar ring; the full and away tensor algebras are
different rings.

## Scope

The algebra `D` need only be a ring with a rational algebra structure.
The argument requires neither finite dimensionality nor faithfulness,
since these are irrelevant to the displayed compatibility equations.
The base morphism and test scheme are arbitrary in one universe. Taking
`T = Over.mk t` gives the pointed comparison at the same field-valued
point `t` and its composite with `b`; an algebraically closed field can
be used for the geometric-point application.

No torsion-order invertibility or finite-etaleness hypothesis is needed
for these algebraic comparisons. The full scalar witness and the coupled
away witness remain explicit, and their independence is not claimed.
The module proves no rational topology result, coherence for composition
of base morphisms, geometric monodromy comparison, Weil pairing
compatibility or invariant PEL level base change.
