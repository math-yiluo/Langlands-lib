import Langlands.Geometry.Analytic.LocalActionLifts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Compact pullbacks in the actual quasi-étale site -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Compact quasi-étale objects have compact binary pullbacks whose underlying
square is a pullback against all localized analytic test objects. -/
def CompactQuasiEtalePullbacksStatement : Prop :=
  ∀ (X : LocalizedCategory.{u, v, v} (K := K))
    (B U V : QuasiEtaleSite X) (f : U ⟶ B) (g : V ⟶ B),
    IsCompactSpace B.left → IsCompactSpace U.left → IsCompactSpace V.left →
      ∃ t : PullbackCone f g, IsCompactSpace t.pt.left ∧
        IsPullback t.fst.left t.snd.left f.left g.left

end Langlands.Analytic.SaturatedAtlasPresentation
