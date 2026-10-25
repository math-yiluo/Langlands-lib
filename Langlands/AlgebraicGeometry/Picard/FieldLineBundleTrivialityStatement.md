# Triviality of line bundles on a field spectrum

`Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityStatement.{u}`
is the proposition

```lean
∀ (K : Type u) [Field K]
  (L : LineBundle (Spec (CommRingCat.of K))),
  Nonempty (L.obj ≅
    Langlands.Scheme.Modules.structureSheaf (Spec (CommRingCat.of K)))
```

The universe `u` is arbitrary. `LineBundle` is the published full subcategory
of actual scheme-module sheaves satisfying `IsLocallyFreeRankOne`: at each
point, restriction to some open neighborhood is isomorphic to that open's
structure sheaf. `L.obj` is the underlying module sheaf, and the target
`structureSheaf` is exactly `SheafOfModules.unit` for the scheme's ring sheaf.
Thus the conclusion is existence of an isomorphism of module sheaves.
It neither chooses a preferred trivialization nor asserts uniqueness.

Only a field and a line bundle are quantified. There is no algebraic-closure
assumption, chosen basis, given global trivialization, tensor inverse, or
additional compatibility premise. The two imports supply the existing
definitions unchanged. This file defines the proposition; it does not prove it.

## Internal derivation and provenance

This is an elementary internal consequence of the local rank-one definition.
The spectrum of a field has exactly one point. A trivializing neighborhood of
that point therefore contains every point and is the top open. The resulting
trivialization of the restricted sheaf can be transported back to the original
scheme along the top-open isomorphism. In the existing interfaces, restriction
can first be compared with pullback using
`Scheme.Modules.restrictFunctorIsoPullback`; the top-open isomorphism,
pullback composition and identity comparisons, and `pullbackUnitIso` then give
the desired global isomorphism. This explains the statement's derivation and
the intended separate proof obligation, rather than providing a Lean proof.
No equivalence between all sheaves and vector spaces is needed for this route.

The original motivation is J. S. Milne, *Abelian Varieties*, 1986 article,
author revision January 2, 2022, Section 6, Corollary 6.4 and its proof,
printed/PDF page 9. On the zero face of the triple product, the factor from
pulling a line bundle back along the constant identity map is written as the
structure sheaf. The internal explanation is that the identity is a rational
point `Spec K → A`; its pullback is a line bundle on `Spec K`, to which the
present proposition applies before pulling back again to the face.
Milne supplies this motivation, but does not explicitly state the general
module-sheaf proposition formalized here. This statement does not assert or
prove Corollary 6.4.

Registered source: `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained source is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`;
the [author's original](https://www.jmilne.org/math/xnotes/AVs.pdf) identifies
the publication. Pages 8–10 were read and the formula on page 9 was checked
visually. No source-specific errata note was present in the project or
Library notes at the time of this statement.

Worker 354 authored the statement and documentation. The implementation route
above also uses Worker 316's shared, unreviewed draft explanation and private
`lineBundle_field_trivial` helper from revision 1 of task
`4db6f774-722f-405b-aeaa-8ab052f17c14`; Worker 316 is credited as a coauthor
for that reused contribution. That draft is a proof-development lead, not an
import or an accepted proof dependency. A separate proof must establish this
exact published proposition and undergo independent semantic review and
exact-target validation.
