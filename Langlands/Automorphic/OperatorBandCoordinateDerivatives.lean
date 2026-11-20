import Langlands.Analysis.UnitGroupFrameDerivatives
import Langlands.Automorphic.OperatorBandProductPatch

/-! # Genuine derivatives in the actual band coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 150000

open scoped Classical ContDiff Matrix.Norms.Operator
open Set

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions

universe u

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance jetsRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance jetsContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance jetsFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance jetsFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance jetsStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

variable (S : OperatorRealization F n)
local instance jetsSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

theorem contDiffOn_coordinateSlice (b : FiniteAdelicGL F n) (v : S.Space) :
    ContDiffOn ℝ ∞ (coordinateSlice F n S b v)
      (range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n)) :=
  coordinateExtension_contDiffOn F n _

private theorem fderiv_coordinateSlice_basis (b : FiniteAdelicGL F n)
    (v : S.Space) (i : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (a : ArchimedeanGL F n) :
    fderiv ℝ (coordinateSlice F n S b v) (a : ArchimedeanMatrix F n)
        ((a : ArchimedeanMatrix F n) * lieBasis F n i) =
      coordinateSlice F n S b (S.envelopingAction (OperatorRealization.basisGenerator F n i) v)
        (a : ArchimedeanMatrix F n) := by
  let f := finiteSmoothSlice F n b (S.ambient v)
  let X := lieDirection F n i
  let d := OperatorRealization.basisGenerator F n i
  have h : finiteSmoothSlice F n b (S.ambient (S.envelopingAction d v)) =
      smoothDifferential F n X f := by
    rw [S.ambient_envelopingAction, finiteSmoothSlice_envelopingAction]
    exact congrArg (fun T : Module.End ℂ (SmoothFunctions F n) => T f)
      (envelopingAction_real_generator F n X)
  change fderiv ℝ (coordinateExtension F n f) (a : ArchimedeanMatrix F n)
      ((a : ArchimedeanMatrix F n) * lieBasis F n i) =
      coordinateExtension F n (finiteSmoothSlice F n b (S.ambient (S.envelopingAction d v))) a
  rw [h, coordinateExtension_apply, smoothDifferential_apply,
    ContinuousMulEquiv.apply_symm_apply]
  exact congrArg (fun Y => fderiv ℝ (coordinateExtension F n f) a ((a : ArchimedeanMatrix F n) * Y))
    (LinearEquiv.apply_symm_apply (realLieAlgebraToMatrix F n) (lieBasis F n i)).symm

set_option backward.isDefEq.respectTransparency true in
/-- A common finite list of genuine enveloping derivatives bounds all
coordinate derivatives through order `N` on the compact matrix region.
The list and constant are uniform over all original vectors and finite
slices. -/
theorem exists_coordinateSlice_jet_bound (t : Set (ArchimedeanMatrix F n)) (ht : IsCompact t)
    (htu : t ⊆ range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n)) (N : ℕ) :
    ∃ (D : Finset (EnvelopingAlgebra F n)) (C : ℝ), 0 ≤ C ∧
      ∀ (b : FiniteAdelicGL F n) (v : S.Space), ∀ x ∈ t, ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (coordinateSlice F n S b v) x‖ ≤ C *
          ∑ d ∈ D, ‖coordinateSlice F n S b (S.envelopingAction d v) x‖ := by
  let A := ArchimedeanMatrix F n
  let I := Fin (Module.finrank ℝ A)
  let M := EnvelopingAlgebra F n
  let aRing : NormedRing A := inferInstanceAs (NormedRing (ArchimedeanMatrix F n))
  let aAlg : NormedAlgebra ℝ A := inferInstanceAs (NormedAlgebra ℝ (ArchimedeanMatrix F n))
  let aDim : FiniteDimensional ℝ A := inferInstanceAs (FiniteDimensional ℝ (ArchimedeanMatrix F n))
  let aComplete : CompleteSpace A := FiniteDimensional.complete ℝ (ArchimedeanMatrix F n)
  let iFinite : Fintype I := Fin.fintype _
  let mMonoid : Monoid M := inferInstanceAs (Monoid (EnvelopingAlgebra F n))
  have hframe := @Langlands.Analysis.UnitGroupFrame.exists_iteratedFDeriv_le_sum_frame
    A I aRing aAlg aDim aComplete iFinite M mMonoid
    (lieBasis F n) (OperatorRealization.basisGenerator F n) t ht htu N
  obtain ⟨D, C, hC, h⟩ := hframe
  refine ⟨D, C, hC, fun b v x hx j hj => ?_⟩
  let f (a : EnvelopingAlgebra F n) :=
    coordinateSlice F n S b (S.envelopingAction a v)
  have hgen : ∀ a i, ∀ y ∈ range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n),
      fderiv ℝ (f a) y (y * lieBasis F n i) =
        f (OperatorRealization.basisGenerator F n i * a) y := by
    rintro a i y ⟨g, rfl⟩
    have he := fderiv_coordinateSlice_basis F n S b (S.envelopingAction a v) i g
    change fderiv ℝ (f a) (g : A) ((g : A) * lieBasis F n i) =
      coordinateSlice F n S b
        (S.envelopingAction (OperatorRealization.basisGenerator F n i * a) v) g
    rw [LinearMap.congr_fun (map_mul S.envelopingAction
      (OperatorRealization.basisGenerator F n i) a) v]
    exact he
  have hb := h f (fun a => contDiffOn_coordinateSlice F n S b (S.envelopingAction a v))
    hgen 1 x hx j hj
  simpa only [f, map_one, Module.End.one_apply, mul_one] using hb

end Langlands.Automorphic.OperatorDeterminantSlice
