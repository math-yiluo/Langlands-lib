# Effective polarized scheme descent for a cartesian étale relation

`PolarizedEtaleRelationEffectivityStatement.{u}` isolates scheme effectivity
without a presheaf or a sheaf representability assumption. Let `p : U → S`
be a surjective étale morphism between affine schemes. Let `E` be an actual
étale equivalence relation with chart `E.U`, relation scheme `E.R`, and
projections `E.t, E.s : E.R → E.U`. Supply a smooth proper morphism
`f : E.U → U` and the cartesian square

```text
E.R  --E.t-->  E.U
 |               |
E.s ; f         f ; p
 |               |
 v               v
 U  ----p---->   S.
```

The square is part of the descent datum, and does not supply a quotient.
For any test scheme, a chart point and a second covering-base coordinate
with the same image in `S` determine a unique relation point. The
reflexivity, symmetry and transitivity laws of `E`, with this uniqueness,
express descent of the chart along `p`. In particular, they express the
usual scheme isomorphism over `U ×_S U` and its cocycle.

Supply `B : EquivariantLineBundle E` whose actual chart bundle is ample.
Its transport gives isomorphisms of actual line bundles for all related
pairs. The identity, transitivity and arbitrary-precomposition laws give
the usual polarization descent datum on the relation and its cocycle.
No choice of a global scheme or a descended polarization is a hypothesis.

The asserted conclusion is an actual scheme `N → S` and a morphism
`q : E.U → N` such that the square with sides `q, f, N.hom, p` is
cartesian and `E.t ; q = E.s ; q`. The cartesian square includes the base
compatibility `q ; N.hom = f ; p`. This is only the scheme-existence and
invariance part of polarized descent: the statement does not assert a
universal quotient property, identify any presheaf, or request a chosen
descended line bundle. Those stronger conclusions are unnecessary for its
intended use, where the original sheaf and its coherent bundle are already
supplied.

This is a derived specialization of the Stacks Project, Section 99.14,
Situation 99.14.1 and Lemmas 99.14.2–3, tag
[0D1L](https://stacks.math.columbia.edu/tag/0D1L). A smooth proper morphism
is flat and of finite presentation, so it meets the source's geometric
hypotheses. A surjective étale morphism between affine schemes is an fppf
cover. Over the affine scheme `U`, absolute ampleness of the chart bundle
is relative ampleness for `f`; properness supplies quasi-compactness. The
relative convention is Definition 29.38.1, tag
[01VH](https://stacks.math.columbia.edu/tag/01VH). The actual equivariant
bundle provides the polarization isomorphisms in the source's morphisms.
The stack property makes this descent datum effective. Forgetting the
descended bundle and geometry retains exactly the conclusion stated here.
The source's effectivity proof uses descent of relative ampleness, Lemma
74.13.1, tag [0D3C](https://stacks.math.columbia.edu/tag/0D3C), which also
ensures that the descended algebraic space is a scheme.

The original HTML for these tags is in registered source
`stacks-polarized-proper-descent-2026-11-14`, snapshot accessed 2026-11-14,
content SHA-256
`b9443e52779eaea7a6c238da47a6195e173e2c6bc8a0bf88a47bd0b892b73e19`.
This module defines the proposition and does not prove it. Its only
universe is the scheme universe; the consumer's independent presheaf value
universe imposes no additional requirement on this geometric statement.
