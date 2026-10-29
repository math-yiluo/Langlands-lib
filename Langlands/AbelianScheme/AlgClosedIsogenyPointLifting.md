# Lifting points through an isogeny over an algebraically closed field

This is an internal prerequisite for the geometric Picard-zero comparison. Its
statement is independent of line bundles, normalized characters and descent.

`Langlands.AbelianScheme.AlgClosedIsogenyPointLiftingStatement` asserts that for
every algebraically closed field `K`, actual abelian schemes `A` and `B` over
`Spec K`, an isogeny `f : A ⟶ B` and a `K`-point `x` of `B`, there is a `K`-point
`a` of `A` whose composite with the actual underlying homomorphism of group
schemes is `x`. Both points and the equality are in `Over (Spec K)`.

The general lemma
`Langlands.exists_point_lift_of_locallyOfFiniteType_surjective` proves the same
lifting assertion for any surjective scheme morphism locally of finite type and
any point valued in an algebraically closed field of the same universe. Pull
back the morphism along that point. The second projection of the pullback is
surjective and locally of finite type over `K`, so the pullback is nonempty and
Jacobson. Its nonempty whole space contains a closed point. Mathlib's
`AlgebraicGeometry.pointOfClosedPoint` turns this closed point into a `K`-point
of the pullback, and `pointOfClosedPoint_comp` says that it is a section of the
second projection. Composing it with the first projection gives the desired
lift by the pullback square.

`Langlands.AbelianScheme.exists_point_lift_of_isogeny` applies that lemma to the
finite and surjective underlying scheme morphism of the isogeny. The structural
map identity for an `Over` morphism shows that the resulting scheme point is
over `K`. `algClosedIsogenyPointLifting` packages this proof as the named
statement.

The proof uses the existing Mathlib closed-point and residue-field construction
in `Mathlib.AlgebraicGeometry.AlgClosed.Basic` and the project's published
finite-flat-surjective definition of isogeny. No reducedness, separability,
étaleness or characteristic assumption is introduced. Flatness and the abelian
scheme geometry are not needed for the general lifting argument. This module
does not prove the Picard-zero criterion or its character-classification input.
