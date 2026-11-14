# Successive supplied coefficient maps of actual formal atlases

This internal construction compares successive extension along supplied algebra
maps with extension along their composite. Its inputs are the actual formal
atlas constructions in `AtlasBaseChangeAlong` and `AtlasBaseChangeComposition`;
it introduces no new assertion from the original literature.

Let `O` be a commutative ring, and let `R`, `S`, `T` be commutative
`O`-algebras in the same universe `v`. Coordinates `σ` are finite. A
`BasicAtlas O R σ` may have an infinite principal cover. Points are the
existing complete compatible families on all coefficient tests, in universe
`v+1`.

For supplied maps `f : R →ₐ[O] S` and `g : S →ₐ[O] T`,
`baseAlongCompOpens_eq` identifies the actual image covers
`g '' (f '' X.opens)` and `(g.comp f) '' X.opens`. This is the
set-theoretic image-composition equality and imposes no flatness or injectivity
condition.

`baseAlongCompIso X f g` is an actual formal atlas isomorphism

```text
(X.baseChangeAlong f).baseChangeAlong g  →  X.baseChangeAlong (g.comp f).
```

It consists of natural formal maps on every localized coefficient test, their
overlap compatibility, and both formal inverse equations. Its formal maps come
from the existing raw composition isomorphism, whose series are the original
transitions between the original charts chosen by successive and direct
extension. This retains the dependence on those actual chart choices.

The implementation first defines `coefficientAlgebra_comp_transport`. An
equality between the induced and supplied scalar structures at `S` identifies
the corresponding structures induced at `T`. The lemma follows by equality
elimination. `baseCompReAlgebraIso` transports the existing `baseCompIso`
at both intermediate and final bases; eliminating the two scalar equalities
reduces the construction to exactly that isomorphism. Its endpoints retain
the exact `reAlgebra` and coefficient-extension atlas data.

For the supplied maps, the tests are `coefficientTest f` and
`coefficientTest g`, and the equalities are `coefficientAlgebraAlong_eq f`
and `coefficientAlgebraAlong_eq g`. The directly restricted test is
definitionally the coefficient test for `g.comp f`; the final equality proofs
are identified by proof irrelevance. This gives the displayed isomorphism
without replacing either endpoint by a point functor.

`baseCompReAlgebra_onPoints` transports the existing raw complete-family
square, again by eliminating the scalar equalities.
`baseAlongComp_onPoints` specializes it: for every `T`-test `A` and every
complete family `x` of `X` on restriction along `g.comp f`, extending first
along `f` on the restriction of `A` along `g`, then along `g`, and applying
the formal comparison gives the direct extension along `g.comp f`.
Successive and direct restriction have definitionally equal coefficient
algebra structures here. `baseAlongComp_inv_onPoints` gives the reverse
equation for the same formal isomorphism, by its induced linear equivalence's
inverse law. These equations concern the entire families at all further
tests, not just one chart.

This pair concerns formal `O`-atlases. Extension of the entire acting order,
special tangent data, height-certified comparison classes, varying-base
moduli, framing, levels, and representability remain separate.
