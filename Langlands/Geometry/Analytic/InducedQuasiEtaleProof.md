# Induction preserves étale and quasi-étale morphisms

Module `Langlands.Geometry.Analytic.InducedQuasiEtaleProof`.

This module proves the Library statement
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.MorphismPropertyStatement`
(module `Langlands.Geometry.Analytic.InducedQuasiEtaleStatement`) as the theorem
`Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace.inductionFunctor_map_quasiEtale_etale`.
The theorem has exactly the type `MorphismPropertyStatement.{u, v, z}`, with the same
universe parameters as the statement. It adds no hypotheses. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The statement: let `K` be a complete ultrametric normed field, `G : Type z` a group, `H` a
subgroup of `G`, and `f : X ⟶ X'` a morphism of
`Action (LocalizedCategory.{u, max z v, max z v}) H`. If `f.hom` is quasi-étale, then so is
`((inductionFunctor H).map f).hom`. If `f.hom` is étale, then so is the induced morphism.

Everything is in the namespace `Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace`.

## The induced morphism as a morphism out of a disjoint union

The underlying object of the induced space `inducedAction H X` is the point of the chosen
disjoint union `copies H X = localizedSigmaCofan (fun _ : G ⧸ H => X.V)`, one copy of `X.V`
for each coset. The inclusion of the copy indexed by `c` is `copy H X c` (module
`InducedAnalyticSpace`).

`inductionFunctor_map_hom_eq_desc` states that

`((inductionFunctor H).map f).hom =
  Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : G ⧸ H => X.V)
    (fun c => f.hom ≫ copy H X' c)`.

Both sides are morphisms out of `copies H X`, so by `copies_hom_ext` it suffices to compare
them after `copy H X c` for every `c`. On the left, `copy_inductionFunctor_map`
(module `InducedSpaceAdjunction`) gives `f.hom ≫ copy H X' c`. On the right,
`Cofan.IsColimit.fac` gives the same morphism.

## The two halves

Write `D` for the right-hand side above. The published statement `SigmaDescStatement`
(module `LocalizedSigmaQuasiEtaleStatement`) is proved in the Library by
`sigmaDesc_quasiEtale_etale` (module `LocalizedSigmaQuasiEtaleProof`). It is applied at the
same universes `u, v, z` to the index type `G ⧸ H : Type z`, the constant family
`fun _ => X.V`, the target `(inducedAction H X').V` and the family
`fun c => f.hom ≫ copy H X' c`. It reduces each half to a property of the components
`f.hom ≫ copy H X' c`.

- The inclusion `copy H X' c` is `(localizedSigmaCofan fun _ => X'.V).inj c`. It is étale by
  `etale_localizedSigmaCofan_inj` (module `LocalizedSigmaComponents`, submitted with this
  proof).
- `quasiEtale_inductionFunctor_map`: if `f.hom` is quasi-étale, each component is
  quasi-étale by `quasiEtale_comp_of_etale` (module `LocalizedQuasiEtaleLocality`):
  a quasi-étale morphism followed by an étale one is quasi-étale. The first part of
  `sigmaDesc_quasiEtale_etale` then makes `D` quasi-étale. After rewriting with
  `inductionFunctor_map_hom_eq_desc`, the induced morphism is quasi-étale.
- `etale_inductionFunctor_map`: if `f.hom` is étale, each component is étale by
  `etale_comp` (module `LocalizedEtaleComposition`). The second part of
  `sigmaDesc_quasiEtale_etale` makes `D` étale, and the same rewriting concludes.

`inductionFunctor_map_quasiEtale_etale` introduces the field, its instances, the group, the
subgroup and `f` from the statement and pairs the two halves.

## Provenance

This is a derived result. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`, §1.2,
Example 1.2.1(i), printed p. 3, uses it without stating it: the functor `U ↦ U_{G/N}` from
the quasi-étale (resp. étale) site of `X(N)` to that of `X_{G/N}(G)` needs induction to
preserve these morphisms. The Library statement's Markdown records this. The proof follows
the route the statement's Markdown anticipates. The induced morphism is the disjoint union of
copies of `f`, and the two properties pass to it because they are local on the source
(Berkovich, *Vanishing cycles for formal schemes*, 1994, registered as
`berkovich-1994-vanishing-cycles-formal-schemes`, §3, printed p. 544, for quasi-étale
morphisms; Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, 1993, registered
as `berkovich-1993-etale-cohomology`, Definition 3.3.4, for étale morphisms). In the Lean proof, this
locality enters only through `SigmaDescStatement` and through the étaleness of the copy
inclusions.
