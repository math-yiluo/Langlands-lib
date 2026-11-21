import Langlands.Global.EisensteinOperatorContinuation
import Langlands.Global.GeneralLinearInfiniteAdelicDifferential

/-! # Concrete operators on the scalar Eisenstein output carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Geometry.Manifold InfiniteAdelicGroupPoints AdelicGroupPoints
open GeneralLinearGroupPoints

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance scalarOperatorGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance scalarOperatorMatrixRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance scalarOperatorMatrixContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance scalarOperatorMatrixAddCommGroup :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

local notation "Forms" => FinitePlotSmoothRationalFunctions F GLG
local notation "scalarValue" => finitePlotSmoothEvaluation F GLG
local notation "ScalarForms" => LinearMap.range (finitePlotSmoothEvaluation F GLG)

private def scalarFiniteSmoothEquiv :
    Langlands.Automorphic.FiniteSmoothRationalFunctions F n ≃ₗ[ℂ] ScalarForms :=
  (finitePlotSmoothGeneralLinearEquiv F n).symm.trans
    (LinearEquiv.ofInjective scalarValue (finitePlotSmoothEvaluation_injective F GLG))

/-- The concrete adelic operator algebra on the scalar values of the actual
finite-smooth rational functions. -/
def scalarFiniteSmoothOperatorAction :
    automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ ScalarForms :=
  ((scalarFiniteSmoothEquiv F n).conjAlgEquiv ℂ).toAlgHom.comp (automorphicOperatorAlgebra F n).val

theorem scalarFiniteSmoothOperatorAction_apply (a : automorphicOperatorAlgebra F n)
    (v : ScalarForms) :
    (scalarFiniteSmoothOperatorAction F n a v).val = scalarAutomorphicOperator F n a v.val := by
  obtain ⟨f, hf⟩ := v.property
  have hv : scalarFiniteSmoothEquiv F n (finitePlotSmoothGeneralLinearEquiv F n f) = v := by
    apply Subtype.ext
    change scalarValue ((finitePlotSmoothGeneralLinearEquiv F n).symm
      (finitePlotSmoothGeneralLinearEquiv F n f)) = v.val
    rw [LinearEquiv.symm_apply_apply]
    exact hf
  funext x
  rw [← hf, scalarAutomorphicOperator_evaluate]
  have he : (scalarFiniteSmoothEquiv F n).symm v = finitePlotSmoothGeneralLinearEquiv F n f := by
    rw [← hv, LinearEquiv.symm_apply_apply]
  change (scalarFiniteSmoothEquiv F n (a.val ((scalarFiniteSmoothEquiv F n).symm v))).val x = _
  rw [he]
  let e := finitePlotSmoothGeneralLinearEquiv F n
  let g := a.val (e f)
  let h := e.symm g
  change evaluate F GLG h.val x = _
  rw [← evaluate_continuousGeneralLinearEquiv_at_point F n h.val]
  change Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
    (e (e.symm g)).val (adelicHomeomorph F n x) =
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n g.val (adelicHomeomorph F n x)
  rw [e.apply_symm_apply]

/-- On the actual smooth carrier, the finite generator is finite right translation. -/
theorem scalarAutomorphicOperator_finite (f : Forms) (b : FiniteAdelicGroupPoints F GLG)
    (x : AdelicGroupPoints F GLG) :
    scalarAutomorphicOperator F n (finiteOperator F n (finiteHomeomorph F n b)) (scalarValue f) x =
      scalarValue f (x * ofFinite F GLG b) := by
  rw [scalarAutomorphicOperator_evaluate]
  change Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
    (finitePlotSmoothGeneralLinearEquiv F n f).val
    (adelicHomeomorph F n x * AdelicGL.ofFinite F n (finiteHomeomorph F n b)) = _
  rw [← adelicHomeomorph_ofFinite, ← map_mul]
  exact evaluate_continuousGeneralLinearEquiv_at_point F n f.val _

/-- On the actual smooth carrier, the compact generator is infinite right translation. -/
theorem scalarAutomorphicOperator_compact (f : Forms) (k : standardInfiniteCompact F n)
    (x : AdelicGroupPoints F GLG) :
    scalarAutomorphicOperator F n (compactOperator F n k) (scalarValue f) x =
      scalarValue f (x * ofInfinite F GLG ((infiniteHomeomorph F n).symm k.val)) := by
  rw [scalarAutomorphicOperator_evaluate]
  let a := (infiniteHomeomorph F n).symm k.val
  have ha : AdelicGL.ofInfinite F n k.val = adelicHomeomorph F n (ofInfinite F GLG a) := by
    rw [adelicHomeomorph_ofInfinite]
    exact congrArg (AdelicGL.ofInfinite F n) ((infiniteHomeomorph F n).apply_symm_apply k.val).symm
  change Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
    (finitePlotSmoothGeneralLinearEquiv F n f).val
    (adelicHomeomorph F n x * AdelicGL.ofInfinite F n k.val) = _
  rw [ha, ← map_mul]
  exact evaluate_continuousGeneralLinearEquiv_at_point F n f.val _

/-- The real generator on an actual scalar slice is the original invariant derivative. -/
theorem scalarAutomorphicOperator_realDirectional {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (X : smoothModel F d) (f : Forms)
    (a : InfiniteAdelicGroupPoints F GLG) (b : FiniteAdelicGroupPoints F GLG) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F GLG hsmooth
    scalarAutomorphicOperator F n
      (differentialOperator F n (ArchimedeanGL.envelopingGenerator F n
        (ArchimedeanGL.complexify F n (infiniteRealLieAlgebraEquiv F n hsmooth X))))
      (scalarValue f) (pair F GLG a b) =
        groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
          (fun g => scalarValue f (pair F GLG g b)) a := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  rw [scalarAutomorphicOperator_evaluate, adelicHomeomorph_pair]
  let g := finitePlotSmoothGeneralLinearEquiv F n f
  let Y := infiniteRealLieAlgebraEquiv F n hsmooth X
  change Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
    (finiteSmoothEnvelopingAction F n
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n Y)) g).val
    (AdelicGL.pair F n (infiniteHomeomorph F n a) (finiteHomeomorph F n b)) = _
  rw [evaluate_finiteSmoothEnvelopingAction, ArchimedeanGL.envelopingAction_real_generator]
  let s := finiteSmoothSlice F n (finiteHomeomorph F n b) g
  have hs : (fun z => s.val (infiniteHomeomorph F n z)) =
      fun z => scalarValue f (pair F GLG z b) := by
    funext z
    rw [finiteSmoothSlice_apply, ← adelicHomeomorph_pair]
    exact evaluate_continuousGeneralLinearEquiv_at_point F n f.val _
  exact (infinite_groupDirectionalValue F n hsmooth X s a).symm.trans
    (congrArg (fun v => groupDirectionalValue 𝓘(ℝ, smoothModel F d) X v a) hs)

end Langlands.Global.EisensteinJet
