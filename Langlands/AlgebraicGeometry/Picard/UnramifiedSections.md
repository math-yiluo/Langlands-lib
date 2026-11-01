# Open immersions into unramified morphisms

This internal derived lemma applies to schemes in arbitrary universe `u`.
If `f` is locally of finite type and formally unramified and `g ≫ f` is
an open immersion, then `g` is an open immersion. In particular, it applies
to sections over open subschemes of the base.

The proof factors `g` through a pullback of the diagonal of `f`, followed
by a base change of `g ≫ f`. Mathlib makes the diagonal an open immersion
under precisely the stated hypotheses. Both factors are therefore open
immersions. This supplies the section argument used in the schematic
closure and birational globalization proofs without adding separation or
finite presentation assumptions.
