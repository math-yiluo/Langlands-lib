import Langlands.AlgebraicGeometry.Picard.FiniteBasisPicardFamily
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceStep
import Langlands.AlgebraicGeometry.NoetherianApproximation.ClosedFiberPolynomialCharts

/-! # An initial Picard source stage over a finite-type integer algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteTypePicardInitialStage

open Langlands.AlgebraicGeometry.Deformation

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  [Algebra.FiniteType ℤ k] [Algebra.FiniteType k K]

/-- A finite-type field point is module finite over the original scalar ring. -/
theorem residueModuleFinite : Module.Finite k K := by
  let : IsJacobsonRing ℤ := NoetherianApproximation.isJacobsonRing_int
  let : IsJacobsonRing k := isJacobsonRing_of_finiteType (A := ℤ) (B := k)
  exact finite_of_finite_type_of_isJacobsonRing k K

local instance : Module.Finite k K := residueModuleFinite
local instance : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))

/-- The chosen complete Noetherian local source presenting the finite tangent test. -/
abbrev sourceRing := ArtinianPolynomialPresentation.ring (FiniteBasisPicardFamily.test f M)

/-- The specified surjective augmentation of the chosen complete local source. -/
abbrev augmentation : sourceRing f M →ₐ[k] K :=
  ArtinianPolynomialPresentation.augmentation (FiniteBasisPicardFamily.test f M)

lemma augmentation_surjective : Function.Surjective (augmentation f M) :=
  ArtinianPolynomialPresentation.augmentation_surjective (FiniteBasisPicardFamily.test f M)

/-- The initial pointed family and its surjective presentation from the chosen source. -/
def stage : ArtinianPicardSourceStep.Stage (augmentation f M) f M where
  test := FiniteBasisPicardFamily.test f M
  cover := ArtinianPolynomialPresentation.cover (FiniteBasisPicardFamily.test f M)
  cover_surjective :=
    ArtinianPolynomialPresentation.cover_surjective (FiniteBasisPicardFamily.test f M)
  augmentation_cover :=
    ArtinianPolynomialPresentation.augmentation_cover (FiniteBasisPicardFamily.test f M)
  family := FiniteBasisPicardFamily.family f M

/-- Every compatible map from the same complete source lifts through every
surjective augmented Artinian test arrow. -/
theorem postcomp_surjective {A B : ArtinianTest k K} (q : A ⟶ B)
    (hq : Function.Surjective (ArtinianTest.toAlgHom q)) :
    Function.Surjective (AugmentedAdicCompletion.postcomp (augmentation f M) q) :=
  CompletedLocalPolynomialSource.postcomp_surjective
    (ArtinianPolynomialPresentation.polynomialAugmentation (FiniteBasisPicardFamily.test f M))
    (ArtinianPolynomialPresentation.polynomialAugmentation_surjective
      (FiniteBasisPicardFamily.test f M)) q hq

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.FiniteTypePicardInitialStage
