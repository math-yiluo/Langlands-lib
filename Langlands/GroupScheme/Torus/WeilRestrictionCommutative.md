# The commutative Weil-restricted multiplicative group

This module equips the published actual group scheme `WeilGm.groupScheme A B`
with the commutativity certificate required by `CommGroupScheme`, so that its
characters and cocharacters use the existing lattice API. Here
`A : CommRingCat.{u}` and `B : Type u` is a commutative `A`-algebra satisfying
`Module.Finite A B` and `Module.Projective A B`.

`isCommMonObj` proves commutativity using the published multiplicative
equivalence from the points over **every** test scheme `T` to
`(B ⊗[A] Γ(T))ˣ`. This unit group is commutative because its underlying ring
is commutative. `commGroupScheme A B` has exactly the existing group scheme
as its underlying group object; it introduces no new coordinate model.
`commPointsEquiv` restates that point equivalence with the commutative object
as codomain, and `commPointsEquiv_naturality` retains restriction along every
morphism of test schemes.

Three isomorphisms package the published comparisons in the commutative
category:

- `commCongrIso e`, for `e : B ≃ₐ[A] B'`, has the same underlying maps as
  `WeilGm.congrIso e`. Both algebras are finite projective over `A`. Its
  point formula is the unit map induced by `e ⊗ id`.
- `commAlgebraBaseChangeIso A B A'`, for a commutative `A`-algebra
  `A' : CommRingCat.{u}`, identifies the actual base change of
  `commGroupScheme A B` with `commGroupScheme A' (A' ⊗[A] B)`. Its point
  formula is `basePointsEquiv A A' B`, the published canonical regrouping
  of the two tensor factors.
- `commSplitIso A I`, for a finite index type `I : Type u`, identifies
  `commGroupScheme A (I → A)` with the published split torus as a
  commutative group scheme. Its point formula is `splitPointsEquiv A I`,
  obtained from `(I → A) ⊗[A] Γ(T) ≃ (I → Γ(T))` and the coordinate
  description of units in a product ring.

This is an internal adapter derived entirely from the published modules
`WeilRestriction`, `WeilRestrictionBaseChange`, `WeilRestrictionSplit`, and
`Lattice`. The inverse laws of the three isomorphisms are exactly the inverse
laws of their existing group-object comparisons. The module proves no new
representability, smoothness, separability, torus descent, or Galois
classification theorem. It preserves arbitrary commutative base rings and
the finite projective hypotheses of those constructions.
