# A finite separable field extension splitting a geometric fibre

`Langlands.AlgebraicGeometry.FiniteEtale.FiniteSeparableFiberSplitStatement`
concerns a field `K`, an algebraically closed extension field `Ω`, and
an actual finite étale cover `Y` of `Spec K`. There is a finite separable
intermediate field `E` of `Ω/K` such that every `Ω`-point of `Y` over `K`
is the restriction of an `E`-point. The theorem `finiteSeparableFiberSplit`
proves this proposition. The theorem `splitFiber_fundamentalGroupMap_smul`
shows that the pointed fundamental group of such an `E` acts trivially
on the original geometric fibre of `Y`.

The geometric fibre functor is a fibre functor in a Galois category by
`geometricGaloisFiberFunctor`. A Galois object `Z` with a point `z` represents
the fibre of `Y` by evaluation at `z`. The coordinate map of `z` into `Ω`
has image a finite-dimensional domain over `K`, hence an intermediate
field `E`. The coordinate algebra of `Z` is finite étale. Its surjection
to the image field preserves formal unramifiedness, which gives separability
of `E/K`. The point `z` factors through `E`, so every point obtained by
evaluating a map from `Z` also factors through `E`.

To prove triviality of the action, regard `Spec E` as a finite étale
cover. The image of its pointed group stabilizes the chosen lift into
that cover. Each point of `Y` is the image of this lift under a morphism
of covers, so naturality of evaluation fixes each point.

This is a derived finite-field-of-definition consequence of the finite
étale fibre-functor description over a field. The source is the Stacks
Project, *Fundamental Groups of Schemes*, Theorem 58.6.2 (tag `0BND`)
and Lemma 58.6.3 (tag `0BNE`), registered as
`stacks-section-58-6-fundamental-groups-2026-11-26`, SHA-256
`11c890588e59a5950ce3fea97a40f5858e166c23169831aac10d2ce2dc11c060`.
