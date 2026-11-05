import Langlands.Automorphic.GeneralLinearFiniteAdelicDifferential
import Langlands.Global.GeneralLinearInfiniteAdelicEnveloping

/-! # Original general-linear finite-smooth enveloping and center comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints
open Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance finiteEnvelopingGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {d : ℕ}

/-- Every actual tangent enveloping differential becomes the original finite-smooth operator. -/
theorem finitePlotSmoothGeneralLinearEquiv_envelopingAction
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG))))
    (f : FinitePlotSmoothRationalFunctions F GLG),
    finitePlotSmoothGeneralLinearEquiv F n (finitePlotSmoothEnvelopingAction F GLG hsmooth hcalc u f) =
      Langlands.Automorphic.finiteSmoothEnvelopingAction F n
        (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc u)
        (finitePlotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc u f
  apply Langlands.Automorphic.finiteSmoothSlice_injective F n
  funext b
  obtain ⟨b, rfl⟩ := (GeneralLinearGroupPoints.finiteHomeomorph F n).surjective b
  dsimp only
  rw [finiteSmoothSlice_finitePlotSmoothGeneralLinearEquiv,
    finitePlotSmoothSlice_envelopingAction,
    GeneralLinearGroupPoints.plotSmoothGeneralLinearEquiv_envelopingAction,
    Langlands.Automorphic.finiteSmoothSlice_envelopingAction,
    finiteSmoothSlice_finitePlotSmoothGeneralLinearEquiv]

/-- Conjugate the actual enveloping action onto the unchanged original finite-smooth carrier. -/
def generalLinearFiniteSmoothEnvelopingAction
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) →
    (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)))) →ₐ[ℂ] Module.End ℂ (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  exact ((finitePlotSmoothGeneralLinearEquiv F n).conjAlgEquiv ℂ).toAlgHom.comp
    (finitePlotSmoothEnvelopingAction F GLG hsmooth hcalc)

/-- On the original carrier, conjugation is the original action composed with the actual algebra comparison. -/
theorem generalLinearFiniteSmoothEnvelopingAction_eq_original
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)),
    generalLinearFiniteSmoothEnvelopingAction F n hsmooth hcalc =
      (Langlands.Automorphic.finiteSmoothEnvelopingAction F n).comp
        (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc).toAlgHom := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  apply AlgHom.ext
  intro u
  apply LinearMap.ext
  intro f
  change finitePlotSmoothGeneralLinearEquiv F n
      (finitePlotSmoothEnvelopingAction F GLG hsmooth hcalc u
        ((finitePlotSmoothGeneralLinearEquiv F n).symm f)) =
    Langlands.Automorphic.finiteSmoothEnvelopingAction F n
      (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc u) f
  rw [finitePlotSmoothGeneralLinearEquiv_envelopingAction, LinearEquiv.apply_symm_apply]

/-- The actual associative center action becomes the original finite-smooth center action. -/
theorem finitePlotSmoothGeneralLinearEquiv_centerAction
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)))))
    (f : FinitePlotSmoothRationalFunctions F GLG),
    finitePlotSmoothGeneralLinearEquiv F n (finitePlotSmoothCenterAction F GLG hsmooth hcalc z f) =
      Langlands.Automorphic.finiteSmoothCenterAction F n
        (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc z)
        (finitePlotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc z f
  exact finitePlotSmoothGeneralLinearEquiv_envelopingAction F n hsmooth hcalc z.val f

/-- Conjugate the actual associative center action onto the unchanged original finite-smooth carrier. -/
def generalLinearFiniteSmoothCenterAction
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) →
    (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG))))) →ₐ[ℂ] Module.End ℂ (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  exact ((finitePlotSmoothGeneralLinearEquiv F n).conjAlgEquiv ℂ).toAlgHom.comp
    (finitePlotSmoothCenterAction F GLG hsmooth hcalc)

/-- The conjugated center action is exactly the original center action under the actual center equivalence. -/
theorem generalLinearFiniteSmoothCenterAction_eq_original
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)),
    generalLinearFiniteSmoothCenterAction F n hsmooth hcalc =
      (Langlands.Automorphic.finiteSmoothCenterAction F n).comp
        (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc).toAlgHom := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  apply AlgHom.ext
  intro z
  apply LinearMap.ext
  intro f
  change finitePlotSmoothGeneralLinearEquiv F n
      (finitePlotSmoothCenterAction F GLG hsmooth hcalc z
        ((finitePlotSmoothGeneralLinearEquiv F n).symm f)) =
    Langlands.Automorphic.finiteSmoothCenterAction F n
      (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc z) f
  rw [finitePlotSmoothGeneralLinearEquiv_centerAction, LinearEquiv.apply_symm_apply]

end Langlands.Automorphic.GroupSchemeFunctions
