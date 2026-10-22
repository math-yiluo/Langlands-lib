# Godement complexes on sites with specified points

Author: Worker 13.

The input is a genuine Mathlib site `(C, J)`, a family of its points, and a
coefficient category with the displayed products and colimits. A point here is
Mathlib's `GrothendieckTopology.Point`: its fiber functor has the filtering and
cover-lifting properties required of a point of the site.

For each point `pᵢ`, Mathlib constructs the inverse-image fiber functor, the
direct-image skyscraper functor, and their adjunction. The degree-zero
functor in this module is the product of the composites:

`C⁰(F) = ∏ᵢ (skyscraperᵢ (fiberᵢ F))`.

The canonical map `F → C⁰(F)` is the product of the adjunction units; its
projection formula is proved. When the fiber functors are jointly faithful,
the map is proved monic: equality after coaugmentation gives equality after
each adjunction unit, the adjunction recovers equality on each fiber, and joint
faithfulness gives equality of the original maps. Under the additional abelian/sheafification
assumptions, the accompanying cokernel construction gives all higher terms,
actual differentials, induced maps of complexes, and the augmentation equation.
This is a construction from sheaves and site points, not a record populated with
assumed cohomology groups or comparison maps.

The formula and cokernel iteration follow Berkovich, *Etale equivariant sheaves
on p-adic analytic spaces*, section 1.5, printed/PDF page 10, items (a)–(b).
That passage uses a discrete family of geometric points and `ν_* ν^*`, the
composite of inverse image followed by direct image. This module
expresses the direct image from the disjoint family as a product of skyscrapers.
It is a derived site-theoretic version of the construction, with coefficient,
point-fiber, indexing, object and morphism universes explicit.

The original was read by Worker 13. The source registration is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The exact member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
It is the supplied unfinished 1995–1996 manuscript.

An arbitrary family of points need not be conservative. Monicity is proved
under the stated joint-faithfulness hypothesis; it is not silently assumed for
an arbitrary family. Exactness, flabbiness, softness and acyclicity require their
appropriate hypotheses and separate proofs.
The geometric points of an actual scheme's small etale site are instantiated
in the companion module. The continuous-action analytic site required by
Berkovich and Harris remains a separate construction; an algebraic etale
specialization is not identified with it.

Formal dependencies are the accompanying `Langlands.Cohomology.CokernelComplex`
and pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`
(Lean 4.34.0), especially `Sites.Point.Skyscraper` and `Sites.Abelian`.
