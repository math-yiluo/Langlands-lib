# Module forms of actual Picard points

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.PointModule`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures.

The actual point fibres `PseudofunctorPointFiber.Points F ξ η Z` of the Library are pairs
of a base map `a : Z.left ⟶ U` and an isomorphism `(F a) ξ ≅ (F Z.hom) η` in the fibre
category. Restriction along `q : Z' ⟶ Z` uses the coherent pullback `pullIso`. This
module expresses points, and their restrictions, through isomorphisms of module sheaves.

## Generic section

Data: a category `C`, a functor `G : C ⥤ Scheme`, a pseudofunctor `F` on schemes with a
module realization `R : ModuleRealization F` (Library `Picard/LineBundleStackDictionary`),
and objects `ξ` over `G U`, `η` over `G T`. The points are those of the reindexed
pseudofunctor `StackPullback.reindex G F` (Library `CategoryTheory/Sites/StackPullback`).

- `modIsoR G R x`: the module isomorphism
  `(G x.1)^* (R.mod ξ) ≅ (G Z.hom)^* (R.mod η)` of a point, namely `R.μIso` of its
  isomorphism.
- `mkPtR G R a ψ`: the point with base map `a` whose isomorphism is
  `R.isoOfIso` of `ψ`, conjugated by the realization's identifications `R.mapIso`.
- `modIsoR_mkPtR`, `mkPtR_modIsoR`: these are mutually inverse.
- `μ_pullHom_reindex`: the module form of `pullHom` for the reindexed pseudofunctor is
  the transport `LineBundleFlatDescent.tr (G.map g)` of the module form. It combines
  `StackPullback.pullHom_reindex` and `ModuleRealization.μ_pullHom`.
- `modIsoR_restrict`: the module isomorphism of `restrict q x` is
  `tr (G.map q.left) _ _ (modIsoR G R x).hom`. `modIsoR_pullIso` is the same statement for
  a pulled-back point with a prescribed base map `b` and `q.left ≫ x.1 = b`.
- `restrict_eq_of_comp`: `restrict q x = ⟨b, pullIso x.2 q.left b Z'.hom hb q.w⟩` for
  every `b` with `hb : q.left ≫ x.1 = b`.

## Relative section

For `f : X ⟶ S`, line bundles `L` on `(relativeSpace f).obj U` and `N` on
`(relativeSpace f).obj T`, and the Library's relative pseudofunctor
`PicardGroupoid.relative f`:

- `modIso f x`: the module isomorphism
  `((relativeSpace f).map x.1)^* L ≅ ((relativeSpace f).map Z.hom)^* N` of a point. It is
  `modIsoR (relativeSpace f) PicardGroupoid.moduleRealization`.
- `modIso_restrict`: `modIso` of a restriction is the transport, as above.

The generic statements are proved for an abstract `F`, so the kernel never unfolds the
concrete Picard pseudofunctor (the same design as `LineBundleStackDictionary`).

## Provenance

Internal infrastructure for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`, built from the
Library's point fibres, module realizations and reindexed pseudofunctors. No literature
statement is formalized.
