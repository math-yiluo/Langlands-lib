# Functorial radius-one comparison of actual affinoid presentations

Author: Worker 56.

This module extends the published objectwise `StrictComparison` construction
to the actual categories of finite quotient presentations and their concrete
multiplicative spectra. Its input is an ultrametric normed field `K`.
No coefficient completeness is needed until the final comparison with the
existing strict spectrum functor.

For a strict presentation `P`, write `E(P) = ofStrict K P` and
`e_P = strictEquiv K P : E(P) -> P`. The imported construction supplies an
algebra equivalence that preserves the quotient norm and is bounded in both
directions. For a bounded algebra map `f : P -> Q`, this module defines

```
ofStrictMap(f) = e_Q^(-1) after f after e_P.
```

Conversely, a bounded map `h : E(P) -> E(Q)` gives
`e_Q after h after e_P^(-1)`. These are actual bounded maps on the quotient
carriers. Their definitions compose the existing maps and their proved
bounds; no new choice of series representatives occurs. Cancelling each
equivalence with its inverse proves that the two operations are mutually
inverse. `strictHomEquiv` packages the resulting equivalence of morphism
types.

`ofStrictFunctor` has object map `E` and morphism map `ofStrictMap`.
Its identity and composition laws follow pointwise by the same inverse
cancellation. `ofStrictFullyFaithful` supplies the explicit inverse on
morphisms, and the `Full` and `Faithful` instances expose surjectivity and
injectivity of the functor's morphism map. Thus every bounded map between
two embedded presentations is the image of exactly one bounded map
between their original strict presentations.

The previously constructed spectrum homeomorphism sends a seminorm `x`
on `P` to the seminorm `a -> x(e_P(a))` on `E(P)`.
`strictSpectrumHomeomorph_naturality` proves that these homeomorphisms
commute with pullback along every bounded algebra map. Evaluating both
sides at `a` reduces the assertion to cancellation of `e_Q` with its
inverse. This result holds without completeness.

`ofStrictSpaceFunctor` is the opposite functor on the categories of
presentations. Under `CompleteSpace K`, `strictSpectrumComparison` is the
natural isomorphism in `TopCat` from the existing
`strictAffinoidSpectrumFunctor K` to
`ofStrictSpaceFunctor K` followed by `affinoidSpectrumFunctor K`.
Its components are exactly the imported concrete spectrum homeomorphisms,
and naturality is the pointwise result just described. The completeness
hypothesis is required by the existing strict spectrum functor, which
factors through complete quotient rings; it is not used by the morphism
transport or the underlying spectrum homeomorphisms.

The construction permits zero variables, the unit ideal and trivially
valued fields. Full faithfulness makes no essential-surjectivity claim:
it does not say that arbitrary positive-polyradius presentations are
strict. It also does not compare arbitrary presentations of an affinoid
algebra, construct analytic atlases or sheaves, or identify analytic sites.

This is a derived categorical construction from the published
`GeneralizedAffinoid/StrictComparison` and `BoundedEquivalence/Definitions`
APIs. Its source motivation is the strict, radius-one case of Berkovich,
*Non-archimedean analytic spaces* (Trieste lectures, 2009), Definition 2.1.2,
printed/PDF page 7, read directly for this contribution. That definition
works with complete coefficient fields and admissible quotient
presentations. The present module transports the already constructed
quotients and bounded morphisms; the functor laws and naturality are
internal consequences of their algebra equivalences, rather than a
separately quoted source theorem. The incomplete-field scope is limited
to these normed constructions.

Registered original: `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.
