import Langlands.AlgebraicGeometry.Deformation.ArtinianDetection
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Gluing

/-! # Detection of affine-target morphisms on local Artinian schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Deformation
namespace ArtinianDetection

/-- The actual scheme probe from a positive quotient of a maximal localization. -/
def probe (R : Type u) [CommRing R] (P : MaximalSpectrum R) (n : ℕ) :
    Spec (CommRingCat.of (LocalTestRing (Localization.AtPrime P.asIdeal) n)) ⟶
      Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime P.asIdeal))))

/-- Morphisms from a noetherian affine scheme to an affine scheme are detected
by its canonical local Artinian probes. -/
theorem spec_hom_ext (R : Type u) [CommRing R] [IsNoetherianRing R]
    {Y : Scheme.{u}} [IsAffine Y] (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ (P : MaximalSpectrum R) (n : ℕ), probe R P n ≫ f = probe R P n ≫ g) :
    f = g := by
  rw [← cancel_mono Y.isoSpec.hom]
  rw [← Spec.map_preimage (f ≫ Y.isoSpec.hom), ← Spec.map_preimage (g ≫ Y.isoSpec.hom)]
  congr 1
  apply CommRingCat.hom_ext
  apply ringHom_ext R
  intro P n
  have h2 : probe R P n ≫ Spec.map (Spec.preimage (f ≫ Y.isoSpec.hom)) =
      probe R P n ≫ Spec.map (Spec.preimage (g ≫ Y.isoSpec.hom)) := by
    rw [Spec.map_preimage, Spec.map_preimage]
    simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ Y.isoSpec.hom) (h P n)
  rw [probe, ← Spec.map_comp, ← Spec.map_comp] at h2
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)

set_option backward.isDefEq.respectTransparency false in
/-- Locally noetherian sources and affine targets admit detection by all
local Artinian test schemes in their own universe. -/
theorem hom_ext {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsAffine Y]
    (f g : X ⟶ Y)
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (t : Spec (CommRingCat.of A) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  apply X.affineCover.hom_ext f g
  intro j
  have : IsLocallyNoetherian (Spec (X.affineOpenCover.X j)) :=
    isLocallyNoetherian_of_isOpenImmersion (X.affineOpenCover.f j)
  have : IsNoetherianRing (X.affineOpenCover.X j) :=
    isLocallyNoetherian_Spec.mp inferInstance
  apply spec_hom_ext (X.affineOpenCover.X j)
  intro P n
  simpa only [Category.assoc] using
    h (LocalTestRing (Localization.AtPrime P.asIdeal) n)
      (probe (X.affineOpenCover.X j) P n ≫ X.affineCover.f j)

end ArtinianDetection
end Langlands.AlgebraicGeometry.Deformation
