import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.ArchimedeanSmoothDifferential
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Mathlib.Analysis.Analytic.Linear

/-! # Smooth and analytic restrictions to a single archimedean place -/

noncomputable section
universe u
open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000
set_option Elab.async false

namespace Langlands.Global.ArchimedeanGL

open RankinSelbergGlobal Langlands.Automorphic

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

/-- Insert a matrix at one real place, with identity matrices at the other places. -/
def realPlaceMatrix (w : RP) (A : RM) : ArchimedeanMatrix F n :=
  placeMatrixHom F n (Pi.mulSingle w A, 1)

/-- Insert a matrix at one complex place, with identity matrices at the other places. -/
def complexPlaceMatrix (w : CP) (A : CM) : ArchimedeanMatrix F n :=
  placeMatrixHom F n (1, Pi.mulSingle w A)

private def realDirection (w : RP) : RM →L[ℝ] ArchimedeanMatrix F n :=
  (realPlaceMatrixInsertion w).toContinuousLinearMap

private def complexDirection (w : CP) : CM →L[ℝ] ArchimedeanMatrix F n :=
  (complexPlaceMatrixInsertion w).toContinuousLinearMap

omit [NumberField F] in
private theorem realDirection_apply (w : RP) (X : RM) :
    realDirection w X = placeMatrixHom F n (Pi.single w X, 0) := by
  refine Matrix.ext fun i j => Prod.ext (funext fun v => ?_) rfl
  change (Pi.single w (X i j) : RP → ℝ) v = (Pi.single w X : RP → RM) v i j
  by_cases h : v = w
  · subst h
    simp
  · simp [h]

omit [NumberField F] in
private theorem complexDirection_apply (w : CP) (X : CM) :
    complexDirection w X = placeMatrixHom F n (0, Pi.single w X) := by
  refine Matrix.ext fun i j => Prod.ext rfl (funext fun v => ?_)
  change (Pi.single w (X i j) : CP → ℂ) v = (Pi.single w X : CP → CM) v i j
  by_cases h : v = w
  · subst h
    simp
  · simp [h]

omit [NumberField F] in
private theorem realPlaceMatrix_eq_add (w : RP) (A : RM) :
    realPlaceMatrix w A = realPlaceMatrixBase w + realDirection w A := by
  refine Matrix.ext fun i j => Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · change (Pi.mulSingle w A : RP → RM) v i j =
      (if v = w then 0 else (1 : RM) i j) + (Pi.single w (A i j) : RP → ℝ) v
    by_cases h : v = w
    · subst h
      simp
    · simp [h]
  · exact (add_zero _).symm

omit [NumberField F] in
private theorem complexPlaceMatrix_eq_add (w : CP) (A : CM) :
    complexPlaceMatrix w A = complexPlaceMatrixBase w + complexDirection w A := by
  refine Matrix.ext fun i j => Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact (add_zero _).symm
  · change (Pi.mulSingle w A : CP → CM) v i j =
      (if v = w then 0 else (1 : CM) i j) + (Pi.single w (A i j) : CP → ℂ) v
    by_cases h : v = w
    · subst h
      simp
    · simp [h]

omit [NumberField F] in
/-- Unit values of the real-place inclusion agree with ambient matrix insertion. -/
theorem realPlaceGL_val (w : RP) (g : RMˣ) :
    (realPlaceGL F n w g : ArchimedeanMatrix F n) = realPlaceMatrix w (g : RM) := by
  refine Matrix.ext fun i j => Prod.ext (funext fun v => ?_) rfl
  change ((Pi.mulSingle w g : RP → RMˣ) v).val i j =
    (Pi.mulSingle w (g : RM) : RP → RM) v i j
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, Units.val_one]

omit [NumberField F] in
/-- Unit values of the complex-place inclusion agree with ambient matrix insertion. -/
theorem complexPlaceGL_val (w : CP) (g : CMˣ) :
    (complexPlaceGL F n w g : ArchimedeanMatrix F n) = complexPlaceMatrix w (g : CM) := by
  refine Matrix.ext fun i j => Prod.ext rfl (funext fun v => ?_)
  change ((Pi.mulSingle w g : CP → CMˣ) v).val i j =
    (Pi.mulSingle w (g : CM) : CP → CM) v i j
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, Units.val_one]

omit [NumberField F] in
/-- The full real-place inclusion restricts to the standard compact inclusion. -/
theorem realPlaceGL_unitary (w : RP) (k : Matrix.unitaryGroup (Fin n) ℝ) :
    realPlaceGL F n w (Unitary.toUnits k) =
      archimedeanGLCoordinates F n (realPlaceCompactInclusion F n w k).val := by
  apply Units.ext
  rw [realPlaceGL_val, coordinates_realPlaceCompactInclusion, realPlaceMatrix_eq_add]
  exact add_comm _ _

omit [NumberField F] in
/-- The full complex-place inclusion restricts to the standard compact inclusion. -/
theorem complexPlaceGL_unitary (w : CP) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    complexPlaceGL F n w (Unitary.toUnits k) =
      archimedeanGLCoordinates F n (complexPlaceCompactInclusion F n w k).val := by
  apply Units.ext
  rw [complexPlaceGL_val, coordinates_complexPlaceCompactInclusion, complexPlaceMatrix_eq_add]
  exact add_comm _ _

private theorem hasFDerivAt_realPlaceMatrix (w : RP) (A : RM) :
    HasFDerivAt (realPlaceMatrix w) (realDirection w) A := by
  rw [funext (realPlaceMatrix_eq_add w)]
  exact ((realDirection w).hasFDerivAt (x := A)).const_add (realPlaceMatrixBase (n := n) w)

private theorem hasFDerivAt_complexPlaceMatrix (w : CP) (A : CM) :
    HasFDerivAt (complexPlaceMatrix w) (complexDirection w) A := by
  rw [funext (complexPlaceMatrix_eq_add w)]
  exact ((complexDirection w).hasFDerivAt (x := A)).const_add
    (complexPlaceMatrixBase (n := n) w)

omit [NumberField F] in
private theorem realPlaceMatrix_mul_realDirection (w : RP) (A B : RM) :
    realPlaceMatrix w A * realDirection w B = realDirection w (A * B) := by
  rw [realDirection_apply, realDirection_apply, realPlaceMatrix,
    ← map_mul (placeMatrixHom F n)]
  congr 1
  refine Prod.ext (funext fun v => ?_) (mul_zero _)
  change (Pi.mulSingle w A : RP → RM) v * (Pi.single w B : RP → RM) v =
    (Pi.single w (A * B) : RP → RM) v
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]

omit [NumberField F] in
private theorem complexPlaceMatrix_mul_complexDirection (w : CP) (A B : CM) :
    complexPlaceMatrix w A * complexDirection w B = complexDirection w (A * B) := by
  rw [complexDirection_apply, complexDirection_apply, complexPlaceMatrix,
    ← map_mul (placeMatrixHom F n)]
  congr 1
  refine Prod.ext (mul_zero _) (funext fun v => ?_)
  change (Pi.mulSingle w A : CP → CM) v * (Pi.single w B : CP → CM) v =
    (Pi.single w (A * B) : CP → CM) v
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]

/-- The inclusion of the full real local group is smooth in the actual unit-group charts. -/
theorem contMDiff_realPlaceGL (w : RP) :
    ContMDiff 𝓘(ℝ, RM) 𝓘(ℝ, ArchimedeanMatrix F n) ∞ (realPlaceGL F n w) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [show (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n) ∘ realPlaceGL F n w =
      realPlaceMatrix w ∘ (Units.val : RMˣ → RM) from funext (realPlaceGL_val w)]
  have h : ContDiff ℝ ∞ (realPlaceMatrix w : RM → ArchimedeanMatrix F n) := by
    rw [funext (realPlaceMatrix_eq_add w)]
    exact contDiff_const.add (realDirection w).contDiff
  exact h.contMDiff.comp Units.contMDiff_val

/-- The inclusion of the full complex local group is smooth over the real matrix charts. -/
theorem contMDiff_complexPlaceGL (w : CP) :
    ContMDiff 𝓘(ℝ, CM) 𝓘(ℝ, ArchimedeanMatrix F n) ∞ (complexPlaceGL F n w) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [show (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n) ∘ complexPlaceGL F n w =
      complexPlaceMatrix w ∘ (Units.val : CMˣ → CM) from funext (complexPlaceGL_val w)]
  have h : ContDiff ℝ ∞ (complexPlaceMatrix w : CM → ArchimedeanMatrix F n) := by
    rw [funext (complexPlaceMatrix_eq_add w)]
    exact contDiff_const.add (complexDirection w).contDiff
  exact h.contMDiff.comp Units.contMDiff_val

/-- The ambient real-place restriction of a coefficient is analytic at each unit
where the original extension is analytic. -/
theorem analyticAt_realPlaceRestriction (w : RP) (f : ArchimedeanMatrix F n → ℂ) (g : RMˣ)
    (hf : AnalyticAt ℝ f (realPlaceGL F n w g : ArchimedeanMatrix F n)) :
    AnalyticAt ℝ (f ∘ realPlaceMatrix w) (g : RM) := by
  have h : (realPlaceMatrix w : RM → ArchimedeanMatrix F n) =
      fun A => realPlaceMatrixBase w + realDirection w A :=
    funext (realPlaceMatrix_eq_add w)
  have ha : AnalyticAt ℝ (realPlaceMatrix w) (g : RM) := by
    rw [h]
    exact analyticAt_const.add ((realDirection w).analyticAt _)
  exact hf.comp_of_eq ha (realPlaceGL_val w g).symm

/-- The ambient complex-place restriction uses the underlying real matrix coordinates. -/
theorem analyticAt_complexPlaceRestriction (w : CP) (f : ArchimedeanMatrix F n → ℂ) (g : CMˣ)
    (hf : AnalyticAt ℝ f (complexPlaceGL F n w g : ArchimedeanMatrix F n)) :
    AnalyticAt ℝ (f ∘ complexPlaceMatrix w) (g : CM) := by
  have h : (complexPlaceMatrix w : CM → ArchimedeanMatrix F n) =
      fun A => complexPlaceMatrixBase w + complexDirection w A :=
    funext (complexPlaceMatrix_eq_add w)
  have ha : AnalyticAt ℝ (complexPlaceMatrix w) (g : CM) := by
    rw [h]
    exact analyticAt_const.add ((complexDirection w).analyticAt _)
  exact hf.comp_of_eq ha (complexPlaceGL_val w g).symm

/-- Local differentiation of the restriction agrees with the inserted real Lie direction. -/
theorem fderiv_realPlaceRestriction (w : RP) (f : SmoothFunctions F n) (g : RMˣ) (X : RM) :
    fderiv ℝ (coordinateExtension F n f ∘ realPlaceMatrix w) (g : RM) ((g : RM) * X) =
      (smoothDifferential F n (realPlaceLieInclusion F n w X) f).val
        ((archimedeanGLCoordinates F n).symm (realPlaceGL F n w g)) := by
  have hs := (coordinateExtension_contDiffAt F n f (realPlaceGL F n w g)).differentiableAt
    (by simp)
  rw [realPlaceGL_val] at hs
  rw [(hs.hasFDerivAt.comp (g : RM) (hasFDerivAt_realPlaceMatrix w (g : RM))).fderiv,
    ContinuousLinearMap.comp_apply, ← realPlaceMatrix_mul_realDirection, smoothDifferential_apply,
    ContinuousMulEquiv.apply_symm_apply, realPlaceGL_val,
    realLieAlgebraToMatrix_realPlaceLieInclusion]
  rfl

/-- The same derivative identity at a complex place uses every complex matrix as a real direction. -/
theorem fderiv_complexPlaceRestriction (w : CP) (f : SmoothFunctions F n) (g : CMˣ) (X : CM) :
    fderiv ℝ (coordinateExtension F n f ∘ complexPlaceMatrix w) (g : CM) ((g : CM) * X) =
      (smoothDifferential F n (complexPlaceLieInclusion F n w X) f).val
        ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w g)) := by
  have hs := (coordinateExtension_contDiffAt F n f (complexPlaceGL F n w g)).differentiableAt
    (by simp)
  rw [complexPlaceGL_val] at hs
  rw [(hs.hasFDerivAt.comp (g : CM) (hasFDerivAt_complexPlaceMatrix w (g : CM))).fderiv,
    ContinuousLinearMap.comp_apply, ← complexPlaceMatrix_mul_complexDirection,
    smoothDifferential_apply, ContinuousMulEquiv.apply_symm_apply, complexPlaceGL_val,
    realLieAlgebraToMatrix_complexPlaceLieInclusion]
  rfl

local notation "RealMatrix" m => Matrix (Fin m) (Fin m) ℝ
local notation "ComplexMatrix" m => Matrix (Fin m) (Fin m) ℂ

/-- Each actual place inclusion is smooth, agrees with the compact inclusion,
preserves analyticity, and carries derivatives to the inserted Lie directions. -/
def PlaceRestrictionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (m : ℕ),
    (∀ w : {v : InfinitePlace K // InfinitePlace.IsReal v},
      ContMDiff 𝓘(ℝ, RealMatrix m) 𝓘(ℝ, ArchimedeanMatrix K m) ∞ (realPlaceGL K m w) ∧
      (∀ k : Matrix.unitaryGroup (Fin m) ℝ, realPlaceGL K m w (Unitary.toUnits k) =
        archimedeanGLCoordinates K m (realPlaceCompactInclusion K m w k).val) ∧
      (∀ (f : ArchimedeanMatrix K m → ℂ) (g : (RealMatrix m)ˣ),
        AnalyticAt ℝ f (realPlaceGL K m w g : ArchimedeanMatrix K m) →
        AnalyticAt ℝ (f ∘ realPlaceMatrix w) (g : RealMatrix m)) ∧
      ∀ (f : SmoothFunctions K m) (g : (RealMatrix m)ˣ) (X : RealMatrix m),
        fderiv ℝ (coordinateExtension K m f ∘ realPlaceMatrix w)
            (g : RealMatrix m) ((g : RealMatrix m) * X) =
          (smoothDifferential K m (realPlaceLieInclusion K m w X) f).val
            ((archimedeanGLCoordinates K m).symm (realPlaceGL K m w g))) ∧
    (∀ w : {v : InfinitePlace K // InfinitePlace.IsComplex v},
      ContMDiff 𝓘(ℝ, ComplexMatrix m) 𝓘(ℝ, ArchimedeanMatrix K m) ∞ (complexPlaceGL K m w) ∧
      (∀ k : Matrix.unitaryGroup (Fin m) ℂ, complexPlaceGL K m w (Unitary.toUnits k) =
        archimedeanGLCoordinates K m (complexPlaceCompactInclusion K m w k).val) ∧
      (∀ (f : ArchimedeanMatrix K m → ℂ) (g : (ComplexMatrix m)ˣ),
        AnalyticAt ℝ f (complexPlaceGL K m w g : ArchimedeanMatrix K m) →
        AnalyticAt ℝ (f ∘ complexPlaceMatrix w) (g : ComplexMatrix m)) ∧
      ∀ (f : SmoothFunctions K m) (g : (ComplexMatrix m)ˣ) (X : ComplexMatrix m),
        fderiv ℝ (coordinateExtension K m f ∘ complexPlaceMatrix w)
            (g : ComplexMatrix m) ((g : ComplexMatrix m) * X) =
          (smoothDifferential K m (complexPlaceLieInclusion K m w X) f).val
            ((archimedeanGLCoordinates K m).symm (complexPlaceGL K m w g)))

theorem placeRestriction : PlaceRestrictionStatement.{u} := by
  intro F _ _ n
  exact ⟨fun w => ⟨contMDiff_realPlaceGL w, realPlaceGL_unitary w,
    analyticAt_realPlaceRestriction w, fderiv_realPlaceRestriction w⟩,
    fun w => ⟨contMDiff_complexPlaceGL w, complexPlaceGL_unitary w,
      analyticAt_complexPlaceRestriction w,
      fderiv_complexPlaceRestriction w⟩⟩

end Langlands.Global.ArchimedeanGL
