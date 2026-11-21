# Field-point image lifting along quasi-étale morphisms

Author: Worker 1004.

`localizedQuasiEtaleFieldPointImageLift` proves exactly
`LocalizedQuasiEtaleFieldPointImageLiftStatement.{u, v, uL} K L`. Here
`K : Type u` is complete and ultrametric, and `L : Type uL` is complete,
ultrametric and algebraically closed with `NormedAlgebra K L`. For a
quasi-étale morphism `f : A ⟶ B` of `LocalizedCategory.{u, v, v} (K := K)` and
an `L`-valued point `p` of `B` whose underlying point lies in the image of `f`,
some `L`-valued point `q` of `A` satisfies
`(localizedFieldPointFunctor L).map f q = p`. The image of `q` is the whole
prescribed field point, including all chart evaluations. No Hausdorff,
compactness or nontrivial-valuation hypothesis is added.

## Pointed lifts

The proof shows a stronger, pointed property. The predicate
`PointedFieldPointLift L f` says: for every `L`-valued point `p` of the target
and every ordinary source point `x` with `f x` equal to the underlying point of
`p`, some `L`-valued point `q` of the source has underlying point exactly `x`
and image exactly `p`. The pointed form is needed because a lift through the
étale part of a quasi-étale chart must land in the given affinoid domain.

The predicate is established in steps.

- `PointedFieldPointLift.comp`: pointed lifts compose. First lift through the
  second map at the image of `x`, then lift through the first map at `x`.
- `pointedFieldPointLift_of_isIso`: an isomorphism `f` has pointed lifts. Take
  `(inv f) p`. Its underlying point is `x`, by the published naturality lemma
  `localizedFieldPointProjection_map_down`.
- `PointedFieldPointLift.of_arrow_iso`: the predicate is invariant under
  isomorphisms in the arrow category, because `g = e.inv.left ≫ f ≫ e.hom.right`.
- `pointedFieldPointLift_localizedDomainInclusion`: the canonical morphism of
  an analytic domain `D` of a saturated presentation has pointed lifts. A full
  field point whose ordinary point lies in `D` restricts to `D`
  (`FieldPoint.restrictOriginalDomain`). The published
  `fieldPoint_map_restrictOriginalDomain` shows that the restriction maps back
  to the original field point.
- `pointedFieldPointLift_of_isAffinoidDomainEmbedding`: by definition an
  affinoid domain embedding is an isomorphism followed by such a domain
  inclusion.
- `pointedFieldPointLift_localizationFunctor_map_of_etale`: the image of an
  all-pieces étale strong map has pointed lifts. Such a map is finite at every
  source point (`hg.isEtale.isQuasifinite`). The published
  `IsFiniteAt.hasFieldPointLiftAt` gives a full field-point lift at the
  prescribed source point. It is applied with the published
  `PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity`.
- `pointedFieldPointLift_of_etale`: localized étale morphisms are arrow-isomorphic
  to such images, by the definition of `etale`.
- `pointedFieldPointLift_localizationFunctor_map_of_quasiEtale`: the image of a
  quasi-étale strong map `g` has pointed lifts. Let `x` be the prescribed point.
  `IsQuasiEtaleAt g x` gives a finite family of chart ranges whose union is a
  neighbourhood of `x`, so `x` lies in one of them, the range of chart `i`. For
  that chart there are an étale `w : W ⟶ B` and an affinoid domain embedding `j`
  of the chart's domain `D` into `W` with `j ≫ w = ν ≫ g`, where `ν` is the
  domain inclusion. The point `x` is `ν x'` for a point `x'` of `D`. The
  composite `j ≫ w` has pointed lifts by the previous steps. Lift `p` at `x'`
  to `q'`, and take `q = ν q'`. Its underlying point is `x`, and
  `g q = (ν ≫ g) q' = (j ≫ w) q' = p`.
- `pointedFieldPointLift_of_quasiEtale`: localized quasi-étale morphisms are
  arrow-isomorphic to such images, by the definition of `quasiEtale`.

Finally, `localizedQuasiEtaleFieldPointImageLift` picks a source point `x` in
the image hypothesis and applies the pointed lift.

## Sources

The mathematical idea follows Berkovich. For an étale morphism the completed
residue field of a point is a finite separable extension of that of its image
(Berkovich 1993, Theorem 3.4.1). Affinoid domains do not change completed
residue fields. A quasi-étale morphism is locally a union of affinoid domains of
spaces étale over the target (Berkovich 1994, §3, printed p.543). So an
embedding into the algebraically closed `L` extends. In Lean, the
residue-field step is entirely contained in the published
`IsFiniteAt.hasFieldPointLiftAt` and `domainCompletedResidueSurjectivity`.
This module only adds the reduction from quasi-étale to étale maps and affinoid
domains, and the transport through localization isomorphisms.
