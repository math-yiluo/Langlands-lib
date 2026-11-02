# Strict-test representations are epimorphisms to complete algebras

Author: Worker 1010.

Fix a normed field K with ultrametric absolute value. Presented strict
affinoid algebras over K are the published `PresentedStrictAffinoidAlgebra K`,
quotients of a strict Tate algebra in finitely many variables by a closed
ideal. Bounded maps are the published `BoundedAlgHom K`.

## Monomial bounds

These are small facts about the published strict Tate algebra API.

- `StrictTateAlgebra.monomialValue_fintype`: over a finite index type σ, the
  published monomial value of a tuple b at an exponent d is the finite product
  of the powers `b i ^ d i`.
- `StrictTateAlgebra.hasBoundedMonomials_of_norm_le_one`: if every entry of a
  tuple b in a normed commutative ring B has norm at most one, then b has
  bounded monomials in the published sense. The bound is `max 1 ‖1‖`. The
  empty monomial is `1`. Any other monomial is a nonempty product of positive
  powers, so its norm is at most one by submultiplicativity.
- `StrictTateAlgebra.hasBoundedMonomials_append`: if tuples
  `b : Fin m → B` and `b' : Fin n → B` have bounded monomials with bounds C and
  C', then their concatenation `Fin.append b b'` has bounded monomials with
  bound `C * C'`. A monomial of the concatenation is the product of a monomial
  of b and a monomial of b'.
- `PresentedStrictAffinoidAlgebra.norm_coordinate_le_one`: every presentation
  coordinate of a presented strict affinoid algebra has norm at most one. It
  is the image of a Tate variable, which has norm one, under the quotient map,
  which does not increase norms.

## The pair test algebra

Let Q be a presented strict affinoid algebra and W a complete normed
commutative K-algebra with ultrametric distance. Let `u v : Q → W` be bounded
K-algebra maps. Write r for the number of presentation coordinates of Q.

- `PairTest.tuple Q u v` is the tuple of 2r elements of W formed by the images
  of the coordinates of Q under u, followed by their images under v.
- `PairTest.hasBoundedMonomials_tuple`: this tuple has bounded monomials. Each
  half is the image of the Tate variables under a bounded map out of the Tate
  algebra, which has bounded monomials by the published
  `hasBoundedMonomials_map_X`; then concatenation is used.
- `PairTest.eval Q u v` is the published evaluation map from the strict Tate
  algebra in 2r variables to W at this tuple.
- `PairTest.algebra Q u v` is the published `ofRelations` presentation whose
  relations are the kernel of this evaluation. As an algebra it is identified
  with the image of the evaluation, the K-algebra of convergent series in the
  images of the coordinates under u and v. Its norm is the quotient norm, which
  may differ from the norm of W.
- `PairTest.toTarget Q u v` is the published `liftRelations` map from the test
  algebra to W sending the coordinates to the tuple.
  `PairTest.toTarget_coordinate` records its value on coordinates.
- `PairTest.toTarget_injective`: this map is injective. An element of the test
  algebra is the image of a Tate series f. If its image in W is zero, then f is
  in the kernel of the evaluation, so f is a relation and its image in the test
  algebra is zero.

The remaining results also assume that K is complete.

- `PairTest.lift Q u v e` evaluates Tate series in r variables at the test
  algebra coordinates selected by `e : Fin r → Fin (2r)`. These coordinates
  have norm at most one, so the published evaluation applies.
- `PairTest.toTarget_comp_lift`: suppose a bounded map `t : Q → W` satisfies
  `tuple Q u v (e k) = t (coordinate k)` for every k. Then `toTarget` composed
  with `lift` equals t composed with the presentation map of Q. Both sides are
  bounded maps out of the Tate algebra that agree on the variables, so the
  published `StrictTateAlgebra.hom_ext` applies.
- `PairTest.inclusion Q u v e t he` is the induced bounded map from Q to the
  test algebra. It is obtained from `lift` by the published
  `BoundedAlgHom.liftQuotient`. A relation f of Q is sent to an element whose
  image in W is `t` of the image of f in Q, which is zero, and injectivity of
  `toTarget` gives that the element is zero.
- `PairTest.toTarget_comp_inclusion`: `toTarget` composed with this inclusion
  equals t. This is checked on images of Tate series.
- `PairTest.left` and `PairTest.right` are the inclusions for the first and the
  last r coordinates, lifting u and v respectively.
  `PairTest.toTarget_comp_left` and `PairTest.toTarget_comp_right` record that
  composing them with `toTarget` gives u and v.

## Epimorphism property

`StrictTestDomain.eq_of_comp_eq` assumes that K is complete and that a bounded
map `i : P → Q` represents a subset U of the Banach spectrum of P for strict
tests, in the sense of the published `StrictTestDomain.Represents`. Let W be
any complete normed commutative K-algebra with ultrametric distance, in any
universe, and let `u v : Q → W` be bounded K-algebra maps with
`u ∘ i = v ∘ i`. Then `u = v`.

Proof. Consider the pair test algebra of u and v.

1. The maps `left ∘ i` and `right ∘ i` agree. After `toTarget`, which is
   injective, they become `u ∘ i` and `v ∘ i`.
2. The map `left ∘ i` has image in U. Every point of the test algebra
   restricts along it to the restriction along i of a point of Q, and the
   restrictions along i of points of Q form exactly U by the second condition
   of `Represents`.
3. By the universal property in `Represents`, there is a unique bounded map
   ψ from Q to the test algebra with `ψ ∘ i = left ∘ i`. Both `left` and `right`
   satisfy this equation, by step 1 for `right`, so both equal ψ.
4. Hence `u = toTarget ∘ left = toTarget ∘ right = v`.

The test algebra is a strict affinoid test even when W is not affinoid. This
is why the universal property for strict tests suffices.

## Provenance

These are internal supporting results for the strict local
rational-neighbourhood step of the Gerritzen–Grauert proof following Temkin
(Math. Ann. 333 (2005)). They replace a completed tensor square of Q over P
by this test algebra, which maps injectively to W. No numbered
external result is claimed.
