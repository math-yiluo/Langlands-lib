# Closed points and rational points over an algebraically closed field

Author: Worker 919.

Module `Langlands.AlgebraicGeometry.ClosedRationalPoints`. This is an internal supporting unit
for Task 7586. It builds on Mathlib (`AlgebraicGeometry.AlgClosed.Basic` and the Jacobson
property of schemes locally of finite type over a field). It needs no literature source. The
first three statements overlap the Library's `SchemeActionRationalPoints`. They are kept here
as the inputs of the Jacobson subset lemma, and they import nothing from the Borel-subgroup
part of the Library.

## Statements

Let `k` be a field and `X : Over (Spec (CommRingCat.of k))` with
`[LocallyOfFiniteType X.hom]`. Write `pt = Over.mk (𝟙 (Spec (CommRingCat.of k)))` and
`cp = IsLocalRing.closedPoint k`.

- `exists_isClosed_mem (U : X.left.Opens) (hU : (U : Set X.left).Nonempty)`:
  `∃ x ∈ U, IsClosed {x}`. Every nonempty open subset contains a closed point.
- With `[IsAlgClosed k]`:
  - `exists_rationalPoint_of_isClosed (z) (hz : IsClosed {z})`: some rational point
    `x : pt ⟶ X` has `x.left cp = z`.
  - `exists_rationalPoint_mem (U) (hU)`: some rational point lands in `U`.
  - `isClosed_rationalPoint (x : pt ⟶ X)`: `IsClosed {x.left cp}`.
  - `subset_singleton_of_rationalPoints` (**Jacobson subset lemma**). Let `Z : Set X.left`
    with `IsLocallyClosed Z`, and `z : pt ⟶ X` with
    `h : ∀ x : pt ⟶ X, x.left cp ∈ Z → x = z`. Then `Z ⊆ {z.left cp}`. A locally closed set
    whose only rational point is `z` contains no other point.

## The implemented proofs

- `exists_isClosed_mem`. `X.left` is a Jacobson space by `LocallyOfFiniteType.jacobsonSpace`,
  since `Spec k` is Jacobson. Then `nonempty_inter_closedPoints` applies to the locally
  closed set `U`.
- `exists_rationalPoint_of_isClosed` is Mathlib's `pointOfClosedPoint` as a morphism over
  `Spec k`. `isClosed_rationalPoint` is the closed-point side of `pointEquivClosedPoint`.
  `exists_rationalPoint_mem` combines the first two.
- `subset_singleton_of_rationalPoints`. Suppose `y ∈ Z` with `y ≠ z.left cp`. The set
  `Z ∩ {z.left cp}ᶜ` is locally closed, because `{z.left cp}` is closed, and it contains
  `y`. Since `X.left` is Jacobson, it contains a closed point `x`. That point comes from a
  rational point `x'`, which lies in `Z`. So `x' = z` by `h`, and `x = z.left cp`, a
  contradiction.
