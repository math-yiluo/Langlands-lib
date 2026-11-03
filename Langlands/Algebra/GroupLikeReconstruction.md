# Reconstruction from group-like elements

Author: Worker 1326.

This internal unit combines Mathlib's linear independence theorem for group-like
elements with its canonical bialgebra homomorphism from the monoid algebra of
those elements. It uses no external structural or splitting theorem.

Let `R` be a commutative domain in universe `u`, and let `A` be a possibly
noncommutative `R`-bialgebra in universe `v`. Assume `A` is torsion-free as an
`R`-module. Evaluation of `R[GroupLike R A]` in `A` is injective:
`linearIndep_groupLikeVal` states that distinct group-like elements are linearly
independent, and evaluation on a monoid-algebra element is its finite linear
combination of those elements. The coefficient map for the monoid algebra is
injective, so equality after evaluation implies equality before evaluation.

If the group-like elements span all of `A`, evaluation is also surjective.
The range of the linear-combination map is exactly the span of its family, and
the values of the bundled `GroupLike` elements are exactly the elements
satisfying `IsGroupLikeElem`. The construction
`Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike` therefore upgrades the
canonical evaluation homomorphism to an actual bialgebra equivalence
`R[GroupLike R A] ≃ₐc[R] A`. It preserves the algebra, counit and
comultiplication, and sends `single g r` to `r • g`.

For any monoid `M` in universe `v`,
`Langlands.MonoidAlgebra.monomialGroupLikeEquiv` identifies `M`
multiplicatively with the group-like elements of `R[M]`. Its forward map is
`m ↦ single m 1`. Injectivity uses `1 ≠ 0` in the domain, and surjectivity is
Mathlib's characterization of group-like elements of a monoid algebra.
Neither finiteness nor commutativity of `M` is required.

In the intended Hopf-algebra application, the group-like elements form a group.
This unit does not assert that they span an arbitrary Hopf algebra, does not
prove any field-extension descent theorem, and does not identify an arbitrary
group scheme with a split torus. Those are separate obligations.
