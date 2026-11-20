# Quasi-étale and étale morphisms out of disjoint unions

Module `Langlands.Geometry.Analytic.LocalizedSigmaQuasiEtaleProof`.

This module proves the Library statement
`Langlands.Analytic.SaturatedAtlasPresentation.SigmaDescStatement` (module
`Langlands.Geometry.Analytic.LocalizedSigmaQuasiEtaleStatement`) as the theorem
`Langlands.Analytic.SaturatedAtlasPresentation.sigmaDesc_quasiEtale_etale`. The statement
says: let `Y : J → LocalizedCategory` be a family of analytic spaces, let `f j : Y j ⟶ Z`, and
let `f̄ = Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f` be the induced morphism out
of their disjoint union. If every `f j` is quasi-étale then `f̄` is quasi-étale, and if every
`f j` is étale then `f̄` is étale. The theorem has exactly the type `SigmaDescStatement.{u, v, z}`,
with the same universe parameters as the statement. It adds no hypotheses, and its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The étale half is `etale_sigmaDesc` from the module
`Langlands.Geometry.Analytic.LocalizedSigmaEtaleDesc`. The quasi-étale half is
`quasiEtale_sigmaDesc` below. It uses the pointwise quasi-étale condition of the module
`Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality` and the domain-embedding lemma
`isDomainEmbedding_sigmaCofan_inj` of the module
`Langlands.Geometry.Analytic.DisjointUnionDomainEmbeddings`.

Everything is in the namespace `Langlands.Analytic.SaturatedAtlasPresentation`; `K` is a complete
ultrametric normed field and `J : Type z`. Write `L` for `localizationFunctor`.

## The component inclusions on points

- `sigmaCofan_inj_baseMap_apply`: for `T : J → SaturatedAtlasPresentation K`, the base map of
  the saturated inclusion `(sigmaCofan T).inj j` sends `x` to `⟨j, x⟩` (by definition).
- `isOpenMap_sigmaCofan_inj_baseMap`: this base map is open (Mathlib's `isOpenMap_sigmaMk`).

## The quasi-étale half

- `quasiEtale_sigmaDesc`: if every `f j` is quasi-étale, then `f̄` is quasi-étale.

  Proof. Put `T j = localizedObjectEquiv.symm (Y j)`, and let `R = rightFractionCoproducts K J`.
  By the Library's construction of `isColimitLocalizedSigmaCofan`, the disjoint union is
  `L (sigmaPresentation T)`, so `f̄` is an arrow `D : L (sigmaPresentation T) ⟶ Z`. By
  `quasiEtale_of_forall_isLocalizedQuasiEtaleAt` it suffices to prove the pointwise condition
  `IsLocalizedQuasiEtaleAt` for `D` at every point `⟨j, x⟩` of the disjoint union.

  1. `f j` is quasi-étale, so it satisfies the pointwise condition at `x`, as an arrow out of
     `T j` (`isLocalizedQuasiEtaleAt_of_quasiEtale`).
  2. The cofan of the Library coproduct includes `Y j` through the nonempty-chart replacement
     `nonemptyReplacement (T j)`: its `j`-th inclusion is `e.inv ≫ L((sigmaCofan T).inj j)`. Here
     `e : L (nonemptyReplacement (T j)) ≅ L (T j)` is the isomorphism `Localization.isoOfHom`
     of the quasi-isomorphism `R.π (T j)`, that is, of `nonemptyReplacementHom (T j)`. Its
     continuous map is the identity
     (`localizedSpaceFunctor_map_localizationFunctor_map_apply`, module
     `LocalizedChartTransport`, together with the fact that the base map of
     `nonemptyReplacementHom` is the identity by definition). So
     `IsLocalizedQuasiEtaleAt.of_iso e` gives the pointwise condition for `e.hom ≫ f j` at `x`.
  3. The factorization property of the colimit (`Cofan.IsColimit.fac`) gives
     `(e.inv ≫ L((sigmaCofan T).inj j)) ≫ D = f j`, hence
     `e.hom ≫ f j = L((sigmaCofan T).inj j) ≫ D` (`Iso.inv_comp_eq`).
  4. The saturated inclusion `(sigmaCofan T).inj j` is a strong domain embedding
     (`isDomainEmbedding_sigmaCofan_inj`) with open base map
     (`isOpenMap_sigmaCofan_inj_baseMap`). So `IsLocalizedQuasiEtaleAt.map_of_isDomainEmbedding`
     pushes the condition forward to the condition for `D` at
     `((sigmaCofan T).inj j).baseMap x = ⟨j, x⟩`.

## The statement

- `sigmaDesc_quasiEtale_etale : SigmaDescStatement.{u, v, z}`: after introducing the data, the
  proof is the pair `⟨quasiEtale_sigmaDesc Y f, etale_sigmaDesc Y f⟩`.

The component inclusion formula comes from `LocalizedSigmaNearness`.
