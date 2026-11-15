import Langlands.Geometry.Analytic.SchemeAnalytificationSpace
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Langlands.Geometry.Analytic.AnalyticDomainSpaces

/-! # Statement: the glued analytification of a scheme is an analytic space -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology SaturatedAtlasPresentation

/-- Statement (Berkovich 1990, proof of Theorem 3.4.1, step (3), for the Library's
polynomial-locus model in its localized category of analytic spaces): for a complete
nonarchimedean nontrivially normed field `K` and a scheme `X` locally of finite type over
`K`, there are a saturated presentation `S`, a homeomorphism `e` from its space to the glued
space `Space K f`, and for every affine open `U` an analytic domain `D U` of `S` with an
isomorphism `φ U` in the localized category from the affine analytification of `U` to the
analytic domain `D U`, such that
1. `e` maps `D U` onto the image of the canonical map `ι K f U`;
2. the underlying map of `φ U` followed by the inclusion of `D U` is `ι K f U` through `e`;
3. for affine opens `V ≤ U`, the morphism of affine analytifications induced by the
   restriction from `U` to `V`, followed by `φ U` and the inclusion of `D U`, is `φ V`
   followed by the inclusion of `D V`. -/
def SchemeAnalytificationAnalyticStructureStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f],
    ∃ (S : SaturatedAtlasPresentation.{u, u, u} K) (e : S.presentation.space ≃ₜ Space K f)
      (D : X.affineOpens → S.AnalyticDomain)
      (φ : ∀ U : X.affineOpens, AffineAnalytification.localized K (chartPresentation K f U) ≅
        localizationFunctor.obj (S.domain (D U))),
      (∀ U : X.affineOpens, e '' (D U).carrier = Set.range (ι K f U)) ∧
      (∀ (U : X.affineOpens) (y : LocalSpace K f U),
        e (localizedSpaceFunctor.map ((φ U).hom ≫ S.localizedDomainInclusion (D U)) y) =
          ι K f U y) ∧
      ∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U),
        AffineAnalytification.localizedHom K (chartPresentation K f U)
            (chartPresentation K f V) (restriction f h) ≫
          (φ U).hom ≫ S.localizedDomainInclusion (D U) =
        (φ V).hom ≫ S.localizedDomainInclusion (D V)

end Langlands.Analytic.SchemeAnalytification
