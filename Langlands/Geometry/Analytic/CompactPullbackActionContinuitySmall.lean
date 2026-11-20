import Langlands.Geometry.Analytic.LocalActionLifts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Basic.UnivLE

/-! # Continuity on compact analytic pullbacks, with small affinoid spectra

This statement replaces `CompactPullbackActionContinuityStatement`: it adds the
explicit hypothesis that every Berkovich spectrum of a presented affinoid algebra
over `K` is small in the space universe `v`. -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G]

/-- If every presented affinoid spectrum over `K` is `v`-small, an action on a
compact analytic pullback is continuous when both projections are equivariant
for continuous actions on the compact factors. -/
def CompactPullbackActionContinuitySmallStatement : Prop :=
  (∀ R : PresentedAffinoidAlgebra K, Small.{v} (BanachSpectrum R)) →
  ∀ (B U V P : LocalizedCategory.{u, v, v} (K := K))
    (f : U ⟶ B) (g : V ⟶ B) (p : P ⟶ U) (q : P ⟶ V),
    IsCompactSpace B → IsCompactSpace U → IsCompactSpace V → IsCompactSpace P →
    IsPullback p q f g →
    ∀ (σ : G →* Aut P) (σU : G →* Aut U) (σV : G →* Aut V),
      IsContinuousAction σU → IsContinuousAction σV →
      (∀ h, (σ h).hom ≫ p = p ≫ (σU h).hom) →
      (∀ h, (σ h).hom ≫ q = q ≫ (σV h).hom) →
      IsContinuousAction σ

omit [CompleteSpace K] in
/-- The smallness hypothesis of `CompactPullbackActionContinuitySmallStatement`
holds whenever the field universe `u` is at most the space universe `v`, for
example in `LocalizedCategory.{u, u, u}`. -/
theorem small_banachSpectrum_of_univLE [UnivLE.{u, v}] :
    ∀ R : PresentedAffinoidAlgebra K, Small.{v} (BanachSpectrum R) :=
  fun _ => inferInstance

end Langlands.Analytic.SaturatedAtlasPresentation
