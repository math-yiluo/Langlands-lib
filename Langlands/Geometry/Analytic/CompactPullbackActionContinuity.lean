import Langlands.Geometry.Analytic.LocalActionLifts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Continuity detected by compact analytic pullback projections -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G]

/-- An action on a compact analytic pullback is continuous when both projections
are equivariant for continuous actions on the compact factors. -/
def CompactPullbackActionContinuityStatement : Prop :=
  ∀ (B U V P : LocalizedCategory.{u, v, v} (K := K))
    (f : U ⟶ B) (g : V ⟶ B) (p : P ⟶ U) (q : P ⟶ V),
    IsCompactSpace B → IsCompactSpace U → IsCompactSpace V → IsCompactSpace P →
    IsPullback p q f g →
    ∀ (σ : G →* Aut P) (σU : G →* Aut U) (σV : G →* Aut V),
      IsContinuousAction σU → IsContinuousAction σV →
      (∀ h, (σ h).hom ≫ p = p ≫ (σU h).hom) →
      (∀ h, (σ h).hom ≫ q = q ≫ (σV h).hom) →
      IsContinuousAction σ

end Langlands.Analytic.SaturatedAtlasPresentation
