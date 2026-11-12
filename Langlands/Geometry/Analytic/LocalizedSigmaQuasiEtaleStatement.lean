import Langlands.Geometry.Analytic.LocalizedDisjointUnion
import Langlands.Geometry.Analytic.QuasiEtaleSite

/-! # Statement: quasi-étale and étale morphisms out of disjoint unions -/

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Statement: a morphism out of a disjoint union of analytic spaces whose restriction to every
piece is quasi-étale (resp. étale) is quasi-étale (resp. étale). -/
def SigmaDescStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (J : Type z)
    (Y : J → LocalizedCategory.{u, max z v, max z v} (K := K))
    (Z : LocalizedCategory.{u, max z v, max z v} (K := K)) (f : ∀ j, Y j ⟶ Z),
    ((∀ j, quasiEtale (f j)) →
        quasiEtale (Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f)) ∧
      ((∀ j, etale (f j)) → etale (Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan Y) f))

end Langlands.Analytic.SaturatedAtlasPresentation
