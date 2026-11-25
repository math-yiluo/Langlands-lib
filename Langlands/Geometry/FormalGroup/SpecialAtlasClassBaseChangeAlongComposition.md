# Successive supplied coefficient maps on actual special-atlas classes

This internal construction completes the supplied-map composition law for
the special-atlas and height-certified comparison quotients. It reuses
`SpecialAtlasClassBaseChangeAlong` and
`AtlasOrderBaseChangeAlongComposition`; no new original-literature
assertion is introduced.

Parameters are a nonarchimedean local field `K`, a finite-dimensional
central division `K`-algebra `D`, a supplied `K`-embedding `ι : L →ₐ[K] D`,
and commutative supplied `𝒪[K]`-algebras `R`, `S`, `T` in the same universe
`v`. A special atlas has coordinates `Fin (reducedDegree K D)`, the
full integer-order action, the existing full-degree unramified
integer-subfield certificate and the actual geometric tangent condition.
This module retains that general-division-algebra interface; existence and
specialization to invariant `1/d` remain separate.

For supplied maps `f : R →ₐ[𝒪[K]] S` and
`g : S →ₐ[𝒪[K]] T`, `baseAlongCompIso X f g` is exactly
`X.order.baseAlongCompIso f g`. Its endpoints are

```text
(X.baseChangeAlong f).baseChangeAlong g  →  X.baseChangeAlong (g.comp f).
```

It uses the actual image-cover equality
`X.atlas.baseAlongCompOpens_eq f g`, and consists of inverse formal
maps commuting with every element of the integer order. The two
complete-family equations, `baseAlongComp_onPoints` and
`baseAlongComp_inv_onPoints`, are exactly the full-order equations.
They compare successive and direct extension at every further
coefficient test. Complete compatible families remain in universe
`v+1`, and covers may be infinite.

`baseAlongCompComparison` supplies a comparison in the existing
refined formal relation. Its left refinement is reflexive. Its right
refinement is reflexive with its generators retargeted by the actual
image-cover equality. Its coordinate isomorphism is the displayed
full-order formal isomorphism restricted to the reflexive cover.
Thus the quotient comparison comes from actual formal maps.

`classOf_baseChangeAlong_comp` applies the existing class equality
criterion to this comparison. Quotient induction then proves
`IsoClass.baseChangeAlong_comp`: successive supplied-map extension
on special-atlas classes equals extension along `g.comp f`.

The same argument works inside `HeightSquaredAtlas`. Both input
representatives already belong to the height-certified subtype, and
each application of `baseChangeAlong` carries its own certificate by
the existing height-preservation theorem. These certificates include
irreducibility of `π`, nilpotence of its actual image in the base,
and the actual chart height `d²` with the scalar-kernel finite locally
free and rank conditions. The proof compares their underlying actual
formal atlases; it never infers height from specialness or from an
arbitrary class equality. The corresponding representative and
quotient composition laws have the same names in
`HeightSquaredAtlas` and `HeightSquaredAtlas.IsoClass`.

No flatness, injectivity or finite-cover hypothesis is imposed.
Together with the previously constructed quotient identity laws,
these are the laws needed for varying-base unframed class functors.
Those functors, their restriction to `Nilp`, the framed Drinfeld
triple functor, polarizations, actions, levels and representability
remain separate constructions.
