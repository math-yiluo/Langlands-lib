# Smoothness descends along a surjective etale map on the source

`Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentStatement.{u}` states
the following implication for arbitrary actual schemes `W`, `X`, and `S`
in universe `u`, and actual morphisms `p : W ⟶ X` and `g : X ⟶ S`:
if `p` is etale and surjective and `p ≫ g` is smooth, then `g` is smooth.
This module defines the proposition; it does not prove it.

The morphism `p` covers the source of `g`. The smoothness hypothesis concerns
the composite into the original target `S`. No base change of the target
is substituted for this composite. The conclusion is Mathlib's scheme
morphism property `AlgebraicGeometry.Smooth g`, which checks the induced
ring maps on all affine opens as specified by its definition. The statement
has no affine, quasi-compact, quasi-separated, reduced, or Noetherian
hypothesis.

## Original source and specialization

The source is the Stacks Project, Descent, Lemma 35.14.5 (Tag
[05B5](https://stacks.math.columbia.edu/tag/05B5)), in the registered folder
`stacks-smooth-etale-source-descent-2026-11-02` (folder SHA-256
`48d0329a769c0531881a211fed43bfd95306a602e134e33ca11d91c03e15f0b9`),
file `05B5.html`.
The original result allows the map covering the source to be any surjective,
flat, locally finitely presented morphism, and asserts descent of both
smoothness and etaleness of the composite. Our statement retains only its
smoothness conclusion and specializes the covering map to an etale map.
Mathlib's etale morphisms are flat and locally of finite presentation,
so this specialization satisfies the source hypotheses.

The original proof first descends local finite presentation and flatness,
then proves smoothness of the fibres by flat surjective descent. This records
the source's route, not an implemented Lean proof. The associated algebraic
space result is Lemma 74.8.4 (Tag
[0AHE](https://stacks.math.columbia.edu/tag/0AHE)), retained as `0AHE.html`
in the same folder; it reduces to the cited scheme lemma. Neither literature
result is assumed as a Lean theorem.

Both originals and their comments were read on 2 November 2026. The two
comments on 05B5 request and announce the algebraic space analogue; they
give no correction to the scheme statement. The 0AHE page has no comments.
No corresponding project errata note was present when the source was read.

## Intended use

The generic smooth relation quotient construction can apply this proposition
to an actual etale scheme atlas of a scheme representing the relation.
Smoothness of its two endpoint composites then descends to the actual
scheme projections. The present statement concerns schemes only and
establishes no quotient, algebraic space, or Picard representability result.
