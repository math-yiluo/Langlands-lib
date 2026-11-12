# Proof of effective descent of four properties from a target étale atlas

The theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.representedAtlasEffectivity`
proves the Library statement
`Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityStatement.{u}`
(`RepresentedAtlasEffectivityStatement.lean`) in every universe `u`. The
statement, its Markdown and its import closure are unchanged. The proof
covers an arbitrary base scheme, arbitrary algebraic spaces, and an arbitrary
target-atlas square. It assumes no prior representability of the space map,
and no finiteness hypotheses beyond the statement.

## Generic reduction

`AtlasEffectivity.etaleAtlasPropertyEffectivity_of_represented` proves
`EtaleAtlasPropertyEffectivity P` for any `P` that is stable under base change
and descends along `Etale ⊓ Surjective`. It assumes that the atlas data
(`IsEtale b`, `IsSurjective b`, the cartesian square
`IsPullback a (h.map q) (hom f) b` and `P q.left`) force every fppf-sheaf
pullback of `hom f` along a scheme test to be represented. The proof runs as
follows.

1. `isRepresentableMorphism_of_pullbacks` (helper module) gives
   `hr : IsRepresentableMorphism (hom f)`.
2. The given square and `hr.isPullback b` are pullbacks of the same cospan.
   `IsPullback.isoIsPullback` therefore gives an isomorphism of their corners,
   and full faithfulness (`Functor.preimageIso`) turns it into an isomorphism
   `e : U ≅ hr.pullback b` over `S` with `e.hom ≫ hr.snd b = q`. Since `P`
   respects isomorphisms, `P (hr.snd b).left` holds.
3. The Library theorem `relativeProperty_of_etale_atlas` concludes the relative
   property on all scheme tests.

## The four properties

The descent instances come from `Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent`:
`closedImmersion_`, `affine_`, `openImmersion_` and
`finite_descendsAlong_etale_surjective`. Mathlib provides base-change
stability. The representability hypothesis is discharged by the lemmas of
`RepresentedAtlasEffectivityDescent.lean` (see its Markdown):

- Closed immersions, affine morphisms and finite morphisms: a closed immersion
  or finite morphism is affine (Mathlib instances), so
  `exists_iso_of_isAffineHom` applies. It glues, over the affine opens of the
  test, the affine-test representations obtained from affine quotients of
  étale equivalence relations.
- Open immersions: `exists_iso_of_isOpenImmersion_test` represents each pullback
  by the open image of the étale-local open immersion, with no affine
  reduction.

## Provenance

The statement cites Stacks Project, *Morphisms of Algebraic Spaces*, Lemmas
12.1 (Tag 03M4), 20.3 (Tag 03WG) and 45.3 (Tag 03ZQ), in the registered
source `stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`. The source
first shows that the morphism is representable, and then descends the
property along the atlas. The Lean proof has the same two-step shape, with the
following routes:

- Representability is proved from the Library's étale-equivalence-relation
  quotients and from open-chart gluing.
- The property itself is descended by the Library's scheme descent instances
  through `relativeProperty_of_etale_atlas`.
