# Rational nonfixed quotient sections from movement on a test scheme

This is an internal rational-density construction. Over an algebraically closed
field of arbitrary characteristic and universe, let `G` be a smooth group,
`i : H → G` a group homomorphism, and `q : G → Q` a flat, surjective,
quasi-compact map to a separated scheme whose fibers on all relative test
schemes are the right cosets of a supplied subgroup `j : P → G`.

`Dynamic.nonfixedQuotientLiftOfMovingTestPoint` takes a rational point `t` of
`H`, an arbitrary relative test scheme `V`, and a point `x : V → G` such that
left multiplication by the constant image of `t` changes `x ≫ q`. It returns
an actual rational lift `g : Spec k → G` for which `g ≫ q` is not fixed on all
tests by the canonical quotient action restricted along `i`.

If every rational lift instead had a fixed quotient section, translation of
`Q` by `t`, composed with `q`, would agree with `q` on every rational point of
`G`. Smoothness makes `G` reduced and locally of finite type. The published
`hom_ext_rationalPoints` therefore identifies the two morphisms because `Q`
is separated. Evaluating their equality at `x` contradicts the supplied
movement. Classical choice selects the resulting rational witness.

The construction uses the actual quotient action and
`SchemeAction.translation` from the Library. No external result is introduced.
It requires no maximal-torus conjugacy, centralizer containment, finiteness of
a Weyl group, properness, or reducedness of `Q`. The moving rational group
element and its moving test point remain inputs. In particular, it does not
assert that an arbitrary proper subgroup quotient has such a test point, nor
does it prove the unconditional positive-root uniqueness statement.
