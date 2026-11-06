import Langlands.Automorphic.GeneralLinearAdelicForms
import Langlands.Automorphic.GroupSchemeFormDifferential
import Langlands.Automorphic.FullOperatorAction

/-! # Uniform adelic forms in the original general-linear differential realization -/

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

local instance uniformFormsGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance uniformFormsGeneralLinearAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance uniformFormsMatrixRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformFormsMatrixContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance uniformFormsMatrixAddCommGroup :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom)
  (hcalc : AdelicDifferentialCommutator F
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) hsmooth)

/-- The original function comparison intertwines the calculus-discharged actual action. -/
theorem finitePlotSmoothGeneralLinearEquiv_actualEnvelopingAction
    (a : AdelicEnvelopingAlgebra F GLG hsmooth)
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    finitePlotSmoothGeneralLinearEquiv F n (actualAdelicEnvelopingAction F GLG hsmooth a f) =
      Langlands.Automorphic.finiteSmoothEnvelopingAction F n
        (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)
        (finitePlotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  exact finitePlotSmoothGeneralLinearEquiv_envelopingAction F n hsmooth hcalc a f

/-- At corresponding original points, the two actual derivatives have identical values. -/
theorem evaluate_generalLinear_actualEnvelopingAction
    (a : AdelicEnvelopingAlgebra F GLG hsmooth)
    (f : FinitePlotSmoothRationalFunctions F GLG) (x : AdelicGroupPoints F GLG) :
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (Langlands.Automorphic.finiteSmoothEnvelopingAction F n
            (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)
            (finitePlotSmoothGeneralLinearEquiv F n f)))
        (GeneralLinearGroupPoints.adelicHomeomorph F n x) =
      evaluate F GLG (actualAdelicEnvelopingAction F GLG hsmooth a f).val x := by
  rw [← finitePlotSmoothGeneralLinearEquiv_actualEnvelopingAction F n hsmooth hcalc]
  exact evaluate_continuousGeneralLinearEquiv_at_point F n
    (actualAdelicEnvelopingAction F GLG hsmooth a f).val x

variable {N : ℕ}
  (rho : GroupScheme.MatrixRepresentation
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (Fin N))

/-- Reindexing all derivatives and all points retains exactly one full adelic exponent. -/
theorem hasAdelicUniformPolynomialGrowth_iff_generalLinear
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    HasAdelicUniformPolynomialGrowth F GLG rho hsmooth hcalc f ↔
      ∃ e : ℕ, ∀ a : ArchimedeanGL.EnvelopingAlgebra F n, ∃ C : ℝ, 0 ≤ C ∧
        ∀ g : AdelicGL F n,
          ‖Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
            (Langlands.Automorphic.finiteSmoothInclusion F n
              (Langlands.Automorphic.finiteSmoothEnvelopingAction F n a
                (finitePlotSmoothGeneralLinearEquiv F n f))) g‖ ≤
            C * RepresentationGrowth.adelicHeight F GLG rho
              ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) ^ e := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  constructor
  · rintro ⟨e, hf⟩
    refine ⟨e, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := (GeneralLinearGroupPoints.infiniteEnvelopingEquiv
      F n hsmooth hcalc).surjective a
    obtain ⟨C, hC, hbound⟩ := hf a
    refine ⟨C, hC, fun g => ?_⟩
    obtain ⟨x, rfl⟩ := (GeneralLinearGroupPoints.adelicHomeomorph F n).surjective g
    rw [evaluate_generalLinear_actualEnvelopingAction,
      (GeneralLinearGroupPoints.adelicHomeomorph F n).symm_apply_apply]
    exact hbound x
  · rintro ⟨e, hf⟩
    refine ⟨e, fun a => ?_⟩
    obtain ⟨C, hC, hbound⟩ := hf
      (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)
    refine ⟨C, hC, fun x => ?_⟩
    have h := hbound (GeneralLinearGroupPoints.adelicHomeomorph F n x)
    rw [evaluate_generalLinear_actualEnvelopingAction,
      (GeneralLinearGroupPoints.adelicHomeomorph F n).symm_apply_apply] at h
    exact h

variable (hrho : GroupScheme.IsClosedSubgroup rho) (hN : 0 < N)
  (hG : GroupScheme.IsConnectedReductive
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))

/-- Include actual uniform forms in the existing original matrix form space. -/
def uniformAdelicAutomorphicGeneralLinearMap :
    (uniformAdelicAutomorphicSubrepresentation F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toSubmodule →ₗ[ℂ] Langlands.Automorphic.AutomorphicForms F n :=
  (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG).comp
    (Submodule.inclusion inf_le_left)

theorem uniformAdelicAutomorphicGeneralLinearMap_injective :
    Function.Injective
      (uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG) :=
  (adelicAutomorphicGeneralLinearMap_injective F n rho hsmooth hcalc hrho hN hG).comp
    (Submodule.inclusion_injective _)

@[simp]
theorem uniformAdelicAutomorphicGeneralLinearMap_val (f : (uniformAdelicAutomorphicSubrepresentation F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toSubmodule) :
    (uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG f).val =
      finitePlotSmoothGeneralLinearEquiv F n f.val := rfl

/-- The restricted injection retains the original full-form enveloping operator. -/
theorem uniformAdelicAutomorphicGeneralLinearMap_envelopingAction
    (a : AdelicEnvelopingAlgebra F GLG hsmooth) (f : (uniformAdelicAutomorphicSubrepresentation F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toSubmodule) :
    uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG
        (uniformAdelicAutomorphicEnvelopingAction F GLG hsmooth hcalc
          (generalLinearStandardInfiniteCompact F n) rho hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN a f) =
      Langlands.Automorphic.automorphicEnvelopingAction F n
        (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc a)
        (uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG f) := by
  apply Subtype.ext
  exact finitePlotSmoothGeneralLinearEquiv_actualEnvelopingAction F n hsmooth hcalc a f.val

/-- The same injection intertwines the unchanged positive finite translations. -/
theorem uniformAdelicAutomorphicGeneralLinearMap_finiteRightAction
    (c : FiniteAdelicGroupPoints F GLG) (f : (uniformAdelicAutomorphicSubrepresentation F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toSubmodule) :
    uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG
        ((uniformAdelicAutomorphicSubrepresentation F GLG (generalLinearStandardInfiniteCompact F n)
          rho hsmooth hcalc hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toRepresentation c f) =
      Langlands.Automorphic.automorphicFiniteRightAction F n
        (GeneralLinearGroupPoints.finiteHomeomorph F n c)
        (uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG f) := by
  apply Subtype.ext
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_finiteRightAction F n f.val.val c

/-- Bundle the injection for every actual enveloping element acting on the original forms. -/
def uniformAdelicAutomorphicGeneralLinearEnvelopingIntertwiner :
    Representation.IntertwiningMap
      (uniformAdelicAutomorphicEnvelopingAction F GLG hsmooth hcalc
        (generalLinearStandardInfiniteCompact F n) rho hG hrho
        (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN).toMonoidHom
      ((Langlands.Automorphic.automorphicEnvelopingAction F n).toMonoidHom.comp
        (GeneralLinearGroupPoints.infiniteEnvelopingEquiv F n hsmooth hcalc).toMonoidHom) where
  toLinearMap := uniformAdelicAutomorphicGeneralLinearMap F n hsmooth hcalc rho hrho hN hG
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    exact uniformAdelicAutomorphicGeneralLinearMap_envelopingAction
      F n hsmooth hcalc rho hrho hN hG a f

end Langlands.Automorphic.GroupSchemeFunctions
