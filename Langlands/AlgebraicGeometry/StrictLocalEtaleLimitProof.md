# Existence of strictly local affine limits of étale neighbourhoods

Workers 252 and 521.

`Langlands.AlgebraicGeometry.strictLocalEtaleLimitExistence.{u}` proves the
published `StrictLocalEtaleLimitExistenceStatement.{u}`. For an affine
scheme `S` and a point `s`, it constructs a `StrictLocalEtaleLimit S s`
whose ring and index category are in universe `u`.

Take the separable closure `Ω` of the scheme residue field at `s`. The
composite `Spec Ω ⟶ Spec κ(s) ⟶ S` gives a geometric point `g` with image
`s`. `PointedAffineEtale.Index g` is a small cofiltered model of the
category of affine schemes étale over `S` with a lift of `g`. Its opposite
indexes the filtered diagram of coordinate rings with compatible maps to
`Ω`. A pointed étale extension of a stage itself gives such a
neighbourhood, and the equivalence with the small model supplies a
refinement realizing the extension.

The ring `A` is the colimit of that diagram. The maps to `Ω` induce a
ring map `A → Ω`. Every element with nonzero field image becomes a unit
in a pointed localization of a stage representing it. This shows that
`A` is local and that the kernel of `A → Ω` is its maximal ideal.
For a monic polynomial over `A`, the finitely many coefficients descend
to a common stage, where the polynomial has a monic lift. Adjoining a
simple root and inverting the derivative produces a pointed standard
étale algebra. Refinement yields a root with the prescribed image in
`Ω`. This proves Hensel's lemma for `A`. For separable closedness, lift
a monic separable irreducible polynomial over the residue field to `A`.
Its image in `Ω` has a simple root, which lifts by the same construction.
Reduction gives a root in the residue field.

The spectrum functor takes the colimiting ring cocone to a limiting
scheme cone. A common refinement shows that its projections have the
same composite to `S`. The closed point of `Spec A` is the image of
the unique point of `Spec Ω`, since the inverse image of the zero ideal
is the maximal ideal of `A`. The composition of `Spec Ω ⟶ Spec A`
with the map to `S` is `g`, so the closed point maps to `s`.

The construction follows the pointed étale colimit approach to strict
henselization. The Lean proof uses the residue-field morphism of `S`
directly and obtains separable closedness by lifting roots. Its conclusion
is the existence of the ring, diagram, limit cone, and map specified by
`StrictLocalEtaleLimit`. [Stacks Project, Algebra, Lemma 10.155.2
(04GP)](https://stacks.math.columbia.edu/tag/04GP), [Lemma 10.155.11
(04GW)](https://stacks.math.columbia.edu/tag/04GW).
