# Pointed morphisms of split tori

Let `k : Type u` be any field. Let `I : Type u` have a finite enumeration
and decidable equality, and let `J : Type u` be finite. Write `T_I` and
`T_J` for the canonical split tori over `Spec k`. Suppose that
`p : T_I.X ⟶ T_J.X` is a morphism of schemes over `Spec k` and that
`η[T_I.X] ≫ p = η[T_J.X]`.

`splitTorus.homOfPointedMorphism` constructs an actual group-scheme
homomorphism `f : T_I ⟶ T_J`. The simp theorem
`splitTorus.homOfPointedMorphism_hom` proves `f.hom.hom = p`.
The constructor chooses the homomorphism whose existence is proved in
`splitTorus.exists_hom_of_pointed_morphism`. The result includes finite fields, every characteristic,
and imperfect fields. No dominance or closed-immersion hypothesis is used.

The proof first evaluates `p` at the universal point with values in the
integer-lattice algebra `AddMonoidAlgebra k (I → ℤ)`. For each target
coordinate, the published unit classification
`IntLatticeAlgebra.exists_eq_single_of_isUnit` expresses the corresponding
unit as a scalar times a single monomial. The private `pointed_one` lemma
uses the identity condition on every test scheme. Evaluating at the family
of identity units then forces the scalar to be one. This proves the public
helper `splitTorus.exists_pointed_coordinate_monomial`.

The public helper `splitTorus.pointed_coordinate_formula` takes a supplied
monomial equation at the universal point and proves that the corresponding
coordinate at an arbitrary affine algebra point `x` is
`∏ i, algebraPointsEquiv I A x i ^ m i`. This helper only needs the supplied
monomial equation; it does not separately require pointedness. Its proof
uses naturality of algebra-valued coordinates and evaluation of the
universal point.

The main theorem forms `f` from the characters corresponding to these
integer exponent vectors, using `characterLatticeEquiv` and the product
universal property. The sum and integer-multiple formulas for characters
show that its affine coordinates have exactly the preceding monomial
values. Injectivity of the coordinate equivalence identifies `f` and `p`
after composition with every affine algebra point. Finally, the affine
coordinate isomorphism of the source split torus supplies one such point
which is an isomorphism, so cancellation gives the desired equality of
scheme morphisms.

This is an internal deduction from the published Laurent unit, universal
point, character lattice, and affine coordinate APIs. It introduces no
external structural assertion. It is a prerequisite for the torus step in
the host rational conjugacy argument; it proves neither splitness of a
general solvable group nor splitness of a unipotent radical, and it does
not prove the full rational maximal-torus conjugacy statement.
