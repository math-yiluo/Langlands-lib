import Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardInitialStage
import Langlands.AlgebraicGeometry.Picard.FiniteBasisPicardTangentLifting
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceCompletion
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerAlgebraization
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerRingLifting
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerTangentLifting
import Langlands.AlgebraicGeometry.Picard.ArtinianPrincipalLifting

/-! # Formally versal Picard line bundles over complete local bases: proof -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation
open PicardGroupoid PicardGroupoid.ArtinianPicardSourceTower
open PicardGroupoid.ArtinianPicardTowerAlgebraization

/-- Every line bundle on a finite-type field fibre of a proper flat scheme over a
finite-type `ℤ`-algebra is the closed fibre of a line bundle over a complete
Noetherian local base that is formally versal at the closed point. -/
theorem finiteTypeFormalVersalBundle : FiniteTypeFormalVersalBundleStatement.{u} := by
  intro R _ _ X hP hF K _ _ _ L₀
  have : Module.Finite R K := FiniteTypePicardInitialStage.residueModuleFinite
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  let f := X.hom
  have : IsProper f := hP
  have : Flat f := hF
  let ε₀ := FiniteTypePicardInitialStage.augmentation f L₀
  have hε₀ : Function.Surjective ε₀ :=
    FiniteTypePicardInitialStage.augmentation_surjective f L₀
  let s₀ := FiniteTypePicardInitialStage.stage f L₀
  have hTL₀ : ArtinianChartVersality.HasLiftingForAt f s₀.family.right.of
      (ArtinianTest.reduction s₀.test) (ArtinianTest.dualReduction R K) :=
    FiniteBasisPicardTangentLifting.hasLiftingForAt f L₀
  have hV : ArtinianChartVersality.IsFormallyVersalAt f (effectiveBundle ε₀ hε₀ f L₀ s₀)
      (residuePoint ε₀ hε₀ f L₀ s₀) :=
    ArtinianPrincipalLifting.isFormallyVersalAt_of_ringLifting f
      (effectiveBundle ε₀ hε₀ f L₀ s₀) (residuePoint ε₀ hε₀ f L₀ s₀)
      (fun q hq c hc N y hy ↦
        ArtinianPicardTowerRingLifting.exists_ringLift ε₀ hε₀ f L₀ s₀
          (fun q hq ↦ FiniteTypePicardInitialStage.postcomp_surjective f L₀ q hq)
          q hq c hc N y hy)
      (ArtinianPicardTowerTangentLifting.hasLiftingForAt_dualReduction ε₀ hε₀ f L₀ s₀ hTL₀)
  exact ⟨limitRing ε₀ hε₀ f L₀ s₀, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, limitAugmentation ε₀ hε₀ f L₀ s₀,
    effectiveBundle ε₀ hε₀ f L₀ s₀, residuePoint ε₀ hε₀ f L₀ s₀,
    limitAugmentation_surjective ε₀ hε₀ f L₀ s₀,
    residuePoint_left ε₀ hε₀ f L₀ s₀, hV,
    ⟨effectiveResidueIso ε₀ hε₀ f L₀ s₀⟩⟩

end Langlands.AlgebraicGeometry.Picard
