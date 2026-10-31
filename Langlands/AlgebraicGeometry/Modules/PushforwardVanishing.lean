import Langlands.AlgebraicGeometry.Modules.PushforwardComparison
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof

/-! # Total cohomology vanishing from vanishing of every direct image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {R : CommRingCat.{u}} (g : Y ⟶ Spec R)

/-- The actual pushforward comparison is an isomorphism whenever all positive
higher direct images of the coefficient vanish. -/
def pushforwardCohomologyIso (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage f (q + 1)).obj M)) (n : ℕ) :
    (relativeCohomology (f ≫ g) n).obj M ≅
      (relativeCohomology g n).obj ((Scheme.Modules.pushforward f).obj M) := by
  haveI := isIso_pushforwardComparison f g M hM
    (fun J hJ q => (pushforwardInjectiveAcyclic X Y f J hJ q).2 R g) n
  exact asIso (pushforwardComparison f g M hM n)

/-- If every direct image, including degree zero, vanishes, all cohomology
over any affine base of the target vanishes. -/
theorem isZero_relativeCohomology_of_higherDirectImage
    (M : X.Modules) (hM : ∀ q : ℕ, IsZero ((higherDirectImage f q).obj M)) (n : ℕ) :
    IsZero ((relativeCohomology (f ≫ g) n).obj M) := by
  have h₀ : IsZero ((Scheme.Modules.pushforward f).obj M) :=
    (hM 0).of_iso ((higherDirectImageZeroIso f).app M).symm
  exact (Langlands.Cohomology.AcyclicComparison.isZero_rightDerived_obj_of_isZero
    (relativeGlobalSections g) n h₀).of_iso
    (pushforwardCohomologyIso f g M (fun q => hM (q + 1)) n)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
