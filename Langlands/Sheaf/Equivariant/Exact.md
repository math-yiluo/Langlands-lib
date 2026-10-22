# Exactness of forgetting equivariance

Author: Worker 61. Builds on the published transport site and abelian
structure (`Langlands.Sheaf.Equivariant.Site`, `Langlands.Sheaf.Equivariant.Abelian`)
and on Worker 13's published left exactness (`Langlands.Sheaf.Equivariant.Limits`).

Let a group `G` act on a topological space `X`. The functor
`toSheaf G X A : TopologicalSheaf G X A ⥤ TopCat.Sheaf A (TopCat.of X)` forgets
the group-labelled transport arrows of an equivariant sheaf and keeps its
restriction to ordinary open inclusions.

- `toSheaf_additive`: for an abelian coefficient category `A` whose ordinary
  sheaves on `X` admit sheafification, `toSheaf G X A` is an additive functor.
  Morphisms of both kinds of sheaves are added on each open, so the equation
  holds by definition.
- `isLocallySurjective_underlyingPresheaf_map`: let `A` be a concrete category
  and let the action be by continuous individual operators. If a morphism `φ`
  of presheaves on the transport category is locally surjective for the
  published transport topology, then its restriction to ordinary opens is
  locally surjective for the ordinary topology of `X`. A transport sieve on the
  object of an ordinary open covers exactly when its label-one inclusions form
  an ordinary cover, and those inclusions form the image sieve of the
  restriction. The proof is this unfolding.
- `toSheaf_preservesEpimorphisms`: let `R` be a commutative ring with `R`, `G`
  and `X` in one universe `u`, and let the action be by continuous individual
  operators. Then `toSheaf G X (ModuleCat.{u} R)` preserves epimorphisms. An
  epimorphism of equivariant module sheaves stays an epimorphism under the
  published equivalence with sheaves on the transport site. By Mathlib's
  `Sheaf.isLocallySurjective_iff_epi'` it is therefore locally surjective. The
  previous lemma makes the underlying morphism locally surjective, and the same
  Mathlib criterion, for the ordinary topology, makes it an epimorphism of
  ordinary sheaves.
- `toSheaf_preservesHomology` and `toSheaf_preservesFiniteColimits`: under the
  same hypotheses, `toSheaf G X (ModuleCat.{u} R)` preserves kernels, cokernels
  and homology, and it preserves finite colimits. These follow from Mathlib's
  `Functor.preservesHomology_of_preservesEpis_and_kernels` and
  `Functor.preservesFiniteColimits_of_preservesHomology`. The kernel hypothesis
  is supplied by Worker 13's published instance `toSheaf_preservesFiniteLimits`.
  With that left exactness instance, `toSheaf` is an exact functor between
  abelian categories.
- `toSheafExactFunctor R G X` packages this as Mathlib's bundled exact functor
  `TopologicalSheaf G X (ModuleCat.{u} R) ⥤ₑ TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X)`
  (`ExactFunctor.of`). Its underlying functor is `toSheaf G X (ModuleCat.{u} R)`
  (`toSheafExactFunctor_obj`).

Provenance: this is the ordinary-topological analogue of an exactness fact
used in Harris's source. In Berkovich, *Etale equivariant sheaves on p-adic
analytic spaces* (unfinished 1995–1996 manuscript), Theorem 1.4.2 (printed and
PDF page 8) states that the inverse image functor for the morphism
`b : X → X(G)` identifies sheaves on the equivariant site `X(G)` with
`G`-sheaves on `X`. Harris, *Galois properties of cohomological automorphic
forms on GL(n)* (1999), section 2, printed page 304, writes Berkovich's
acyclic functor as a composite of `ν_* ν^*` and `b^*` and records that
Berkovich verifies both functors are exact. Here `toSheaf` plays the role of
`b^*` followed by forgetting the `G`-action, on the ordinary-topological
transport site rather than Berkovich's analytic equivariant étale site. No
smoothness or discreteness condition on the action is used or claimed. The
proof route through local surjectivity is this module's own.

Sources: registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`) and
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`
(SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`).
Worker 61 read the cited passages. Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
