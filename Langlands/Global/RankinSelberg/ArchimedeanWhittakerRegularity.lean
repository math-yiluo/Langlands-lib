import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerBasic
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.RankinSelberg.CuspCentralBound

/-!
# Archimedean regularity of global Whittaker functions

Let `T` be an actual cuspidal realization of `GL_(r+1)` over a number field, `ψ` a standard
additive character, `w` a vector of `T` and `b` a finite adelic point. In its set-integral form
over the Borel fundamental domain of `N(F)` in `N(𝔸)`, the Whittaker function
`g ↦ W_w((g, b))` of the invertible archimedean matrices `g` extends to all archimedean matrices
`M` (`archWhittakerExt`): replace the cusp function by the archimedean slice of
`x ↦ φ_w(x · (M, b))` in matrix coordinates. This extension is infinitely differentiable on the
invertible matrices. Its derivative at `g` in the direction `g Z` is the extension for the
enveloping derivative `R(Z) w`. Every Whittaker function of `T` is bounded by a constant times
a fixed power of `|det|`. See the paired Markdown.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj Matrix.Norms.Operator ContDiff Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints Langlands.Automorphic Langlands.Automorphic.ContinuousRationalFunctions

local instance regSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance regSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance regRationalAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance regContinuousAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance regSmoothAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance regFormsAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance regStableAddCommGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance regRealizationAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

section Points

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

theorem adelicHomeomorph_adelicPoint (g : ArchimedeanGL F n) (a : FiniteAdelicGL F n) :
    GeneralLinearGroupPoints.adelicHomeomorph F n (adelicPoint F n g a) =
      AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm g) *
        AdelicGL.ofFinite F n a :=
  ((GeneralLinearGroupPoints.adelicEquiv F n).apply_symm_apply _).trans
    (OperatorRealization.pair_eq_ofInfinite_mul_ofFinite _ _)

theorem detNorm_adelicPoint (g : ArchimedeanGL F n) (a : FiniteAdelicGL F n) :
    detNorm F n (adelicPoint F n g a) =
      absDet F n (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm g)) *
        absDet F n (AdelicGL.ofFinite F n a) := by
  rw [CuspCentralBound.detNorm_eq_absDet, adelicHomeomorph_adelicPoint, absDet_mul]

theorem continuous_detNorm_adelicPoint (a : FiniteAdelicGL F n) :
    Continuous fun g : ArchimedeanGL F n => detNorm F n (adelicPoint F n g a) := by
  simp only [detNorm_adelicPoint]
  exact (((continuous_absDet F n).comp (map_continuous (AdelicGL.ofInfinite F n))).comp
    (map_continuous (archimedeanGLCoordinates F n).symm)).mul continuous_const

end Points

section Coordinates

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The archimedean component of an adelic point, in matrix coordinates. -/
def archPart (x : Points F n) : ArchimedeanGL F n :=
  archimedeanGLCoordinates F n
    (AdelicGL.infinite F n (GeneralLinearGroupPoints.adelicHomeomorph F n x))

/-- The finite component of an adelic point. -/
def finPart (x : Points F n) : FiniteAdelicGL F n :=
  AdelicGL.finite F n (GeneralLinearGroupPoints.adelicHomeomorph F n x)

theorem archimedeanGLCoordinates_infinite_mul (x : Points F n) (g : ArchimedeanGL F n) :
    archimedeanGLCoordinates F n
        (AdelicGL.infinite F n (GeneralLinearGroupPoints.adelicHomeomorph F n x) *
          (archimedeanGLCoordinates F n).symm g) = archPart F n x * g := by
  rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- The `k`-th coordinate functional of the chosen real basis of the archimedean matrices. -/
def coordFunctional (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) :
    ArchimedeanMatrix F n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (ArchimedeanMatrix F n)).coord k)

/-- The continuous linear map `A ↦ (V ↦ e*_k(A V))`. -/
def leftCoord (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) :
    ArchimedeanMatrix F n →L[ℝ] (ArchimedeanMatrix F n →L[ℝ] ℂ) :=
  ((ContinuousLinearMap.smulRightL ℝ (ArchimedeanMatrix F n) ℂ).flip 1).comp
    ((ContinuousLinearMap.compL ℝ (ArchimedeanMatrix F n) (ArchimedeanMatrix F n) ℝ
      (coordFunctional F n k)).comp (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix F n)))

/-- The functional `V ↦ e*_k(M⁻¹ V)`, with `Ring.inverse`. -/
def invCoord (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) (M : ArchimedeanMatrix F n) :
    ArchimedeanMatrix F n →L[ℝ] ℂ :=
  leftCoord F n k (Ring.inverse M)

theorem invCoord_apply (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (M V : ArchimedeanMatrix F n) :
    invCoord F n k M V =
      (((Module.finBasis ℝ (ArchimedeanMatrix F n)).repr (Ring.inverse M * V) k : ℝ) : ℂ) := by
  simp [invCoord, leftCoord, coordFunctional]

theorem contDiffOn_invCoord (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) {m : WithTop ℕ∞} :
    ContDiffOn ℝ m (invCoord F n k) {M : ArchimedeanMatrix F n | IsUnit M} := by
  rintro _ ⟨u, rfl⟩
  exact ((leftCoord F n k).contDiff.contDiffAt.comp _
    (contDiffAt_ringInverse ℝ u)).contDiffWithinAt

end Coordinates

section PointAlgebra

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

theorem adelicEquiv_eq_pair (x : Points F n) :
    GeneralLinearGroupPoints.adelicEquiv F n x =
      AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm (archPart F n x)) (finPart F n x) :=
  (AdelicGL.pair_projections F n _).symm.trans
    (congrArg (fun a => AdelicGL.pair F n a (finPart F n x))
      ((archimedeanGLCoordinates F n).symm_apply_apply _).symm)

theorem mul_adelicPoint (x : Points F n) (g : ArchimedeanGL F n) (b : FiniteAdelicGL F n) :
    x * adelicPoint F n g b = adelicPoint F n (archPart F n x * g) (finPart F n x * b) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  have e1 := map_mul (GeneralLinearGroupPoints.adelicEquiv F n) x (adelicPoint F n g b)
  have e2 : GeneralLinearGroupPoints.adelicEquiv F n (adelicPoint F n g b) =
      AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm g) b :=
    MulEquiv.apply_symm_apply _ _
  have e3 : GeneralLinearGroupPoints.adelicEquiv F n
      (adelicPoint F n (archPart F n x * g) (finPart F n x * b)) =
      AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm (archPart F n x * g))
        (finPart F n x * b) :=
    MulEquiv.apply_symm_apply _ _
  have e4 := AdelicGL.pair_mul F n ((archimedeanGLCoordinates F n).symm (archPart F n x))
    ((archimedeanGLCoordinates F n).symm g) (finPart F n x) b
  have e5 : (archimedeanGLCoordinates F n).symm (archPart F n x * g) =
      (archimedeanGLCoordinates F n).symm (archPart F n x) *
        (archimedeanGLCoordinates F n).symm g := map_mul _ _ _
  rw [e1, e2, e3, adelicEquiv_eq_pair, e4, e5]

theorem adelicEquiv_adelicPoint (g : ArchimedeanGL F n) (a : FiniteAdelicGL F n) :
    GeneralLinearGroupPoints.adelicEquiv F n (adelicPoint F n g a) =
      AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm g) a :=
  MulEquiv.apply_symm_apply _ _

theorem archPart_adelicPoint (g : ArchimedeanGL F n) (a : FiniteAdelicGL F n) :
    archPart F n (adelicPoint F n g a) = g :=
  (congrArg (fun y => archimedeanGLCoordinates F n (AdelicGL.infinite F n y))
    (adelicEquiv_adelicPoint F n g a)).trans
      (by rw [AdelicGL.infinite_pair, ContinuousMulEquiv.apply_symm_apply])

theorem finPart_adelicPoint (g : ArchimedeanGL F n) (a : FiniteAdelicGL F n) :
    finPart F n (adelicPoint F n g a) = a :=
  (congrArg (fun y => AdelicGL.finite F n y) (adelicEquiv_adelicPoint F n g a)).trans
    (AdelicGL.finite_pair F n _ _)

end PointAlgebra

section Slice

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

theorem cuspFunction_adelicPoint (w : T.Space) (g : ArchimedeanGL F (r + 1))
    (b : FiniteAdelicGL F (r + 1)) :
    cuspFunction F T w (adelicPoint F (r + 1) g b) =
      evaluate F (r + 1) (T.realization.toContinuous w)
        (AdelicGL.ofInfinite F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm g) *
          AdelicGL.ofFinite F (r + 1) b) :=
  (Unfolding.cuspFunction_apply_eq F T w _).trans
    (congrArg (evaluate F (r + 1) (T.realization.toContinuous w))
      (adelicHomeomorph_adelicPoint F (r + 1) g b))

theorem cuspFunction_mul_adelicPoint (w : T.Space) (x : Points F (r + 1))
    (g : ArchimedeanGL F (r + 1)) (b : FiniteAdelicGL F (r + 1)) :
    cuspFunction F T w (x * adelicPoint F (r + 1) g b) =
      evaluate F (r + 1) (T.realization.toContinuous w)
        (AdelicGL.ofInfinite F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm
            (archPart F (r + 1) x * g)) *
          AdelicGL.ofFinite F (r + 1) (finPart F (r + 1) x * b)) :=
  (congrArg (cuspFunction F T w) (mul_adelicPoint F (r + 1) x g b)).trans
    (cuspFunction_adelicPoint T w _ _)

/-- The enveloping derivative `R(Z) w` of a vector in the real matrix direction `Z`. -/
def lieDeriv (Z : ArchimedeanMatrix F (r + 1)) (w : T.Space) : T.Space :=
  T.realization.envelopingAction (Unfolding.matrixGenerator F (r + 1) Z) w

/-- For fixed `w` and `y`, the value `φ_(R(a) w)(y)` is complex-linear in `a`. -/
def envelopingValue (w : T.Space) (y : Points F (r + 1)) :
    ArchimedeanGL.EnvelopingAlgebra F (r + 1) →ₗ[ℂ] ℂ :=
  (LinearMap.proj y).comp ((Unfolding.cuspLinear F T).comp
    ((LinearMap.applyₗ w).comp T.realization.envelopingAction.toLinearMap))

/-- For fixed `w` and `y`, the value `φ_(R(Z) w)(y)` is real-linear in `Z`. -/
def lieDerivValue (w : T.Space) (y : Points F (r + 1)) :
    ArchimedeanMatrix F (r + 1) →ₗ[ℝ] ℂ where
  toFun Z := envelopingValue T w y (Unfolding.matrixGenerator F (r + 1) Z)
  map_add' Z₁ Z₂ :=
    (congrArg (envelopingValue T w y) (Unfolding.matrixGenerator_add F (r + 1) Z₁ Z₂)).trans
      (map_add _ _ _)
  map_smul' c Z :=
    (congrArg (envelopingValue T w y) (Unfolding.matrixGenerator_smul F (r + 1) c Z)).trans
      ((map_smul _ _ _).trans (Complex.real_smul).symm)

theorem lieDerivValue_apply (w : T.Space) (y : Points F (r + 1)) (Z : ArchimedeanMatrix F (r + 1)) :
    lieDerivValue T w y Z = cuspFunction F T (lieDeriv T Z w) y := rfl

theorem cuspFunction_lieDeriv_eq_sum (Z : ArchimedeanMatrix F (r + 1)) (w : T.Space)
    (y : Points F (r + 1)) :
    cuspFunction F T (lieDeriv T Z w) y =
      ∑ k, (((Module.finBasis ℝ (ArchimedeanMatrix F (r + 1))).repr Z k : ℝ) : ℂ) *
        cuspFunction F T (lieDeriv T (Module.finBasis ℝ (ArchimedeanMatrix F (r + 1)) k) w) y := by
  have h := congrArg (lieDerivValue T w y)
    ((Module.finBasis ℝ (ArchimedeanMatrix F (r + 1))).sum_repr Z)
  rw [map_sum] at h
  simp only [map_smul, Complex.real_smul, lieDerivValue_apply] at h
  exact h.symm

/-- The archimedean slice of `x ↦ φ_w(x · (M, b))`, extended to all archimedean matrices `M`. -/
def sliceIntegrand (w : T.Space) (b : FiniteAdelicGL F (r + 1)) (x : Points F (r + 1))
    (M : ArchimedeanMatrix F (r + 1)) : ℂ :=
  ArchimedeanGL.coordinateExtension F (r + 1)
    (finiteSmoothSlice F (r + 1) (finPart F (r + 1) x * b) (T.realization.ambient w))
    ((archPart F (r + 1) x : ArchimedeanMatrix F (r + 1)) * M)

theorem sliceIntegrand_units (w : T.Space) (b : FiniteAdelicGL F (r + 1)) (x : Points F (r + 1))
    (g : ArchimedeanGL F (r + 1)) :
    sliceIntegrand T w b x (g : ArchimedeanMatrix F (r + 1)) =
      cuspFunction F T w (x * adelicPoint F (r + 1) g b) :=
  (congrArg (ArchimedeanGL.coordinateExtension F (r + 1)
      (finiteSmoothSlice F (r + 1) (finPart F (r + 1) x * b) (T.realization.ambient w)))
      (Units.val_mul (archPart F (r + 1) x) g).symm).trans
    ((ArchimedeanGL.coordinateExtension_apply F (r + 1) _ (archPart F (r + 1) x * g)).trans
      ((T.realization.finiteSmoothSlice_ambient_apply w (finPart F (r + 1) x * b) _).trans
        (cuspFunction_mul_adelicPoint T w x g b).symm))

theorem fderiv_coordinateExtension_slice (w : T.Space) (y : FiniteAdelicGL F (r + 1))
    (g : ArchimedeanGL F (r + 1)) (V : ArchimedeanMatrix F (r + 1)) :
    fderiv ℝ (ArchimedeanGL.coordinateExtension F (r + 1)
        (finiteSmoothSlice F (r + 1) y (T.realization.ambient w)))
        (g : ArchimedeanMatrix F (r + 1)) V =
      evaluate F (r + 1) (T.realization.toContinuous
          (lieDeriv T (((g⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) * V) w))
        (AdelicGL.ofInfinite F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm g) *
          AdelicGL.ofFinite F (r + 1) y) := by
  set Z := ((g⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) * V with hZ
  set f := finiteSmoothSlice F (r + 1) y (T.realization.ambient w) with hf
  have h := Unfolding.smoothDifferential_slice F T.realization w Z y
    ((archimedeanGLCoordinates F (r + 1)).symm g)
  have h2 := ArchimedeanGL.smoothDifferential_apply F (r + 1)
    ((ArchimedeanGL.realLieAlgebraToMatrix F (r + 1)).symm Z) f
    ((archimedeanGLCoordinates F (r + 1)).symm g)
  have e1 : archimedeanGLCoordinates F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm g) = g :=
    ContinuousMulEquiv.apply_symm_apply _ _
  have e2 : ArchimedeanGL.realLieAlgebraToMatrix F (r + 1)
      ((ArchimedeanGL.realLieAlgebraToMatrix F (r + 1)).symm Z) = Z :=
    LinearEquiv.apply_symm_apply _ _
  have e3 : (g : ArchimedeanMatrix F (r + 1)) * Z = V := by
    rw [hZ, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [e1, e2, e3] at h2
  exact h2.symm.trans h

/-- The candidate derivative of `sliceIntegrand` at an invertible `M`. -/
def sliceDeriv (w : T.Space) (b : FiniteAdelicGL F (r + 1)) (x : Points F (r + 1))
    (M : ArchimedeanMatrix F (r + 1)) : ArchimedeanMatrix F (r + 1) →L[ℝ] ℂ :=
  ∑ k, sliceIntegrand T (lieDeriv T (Module.finBasis ℝ (ArchimedeanMatrix F (r + 1)) k) w) b x M •
    invCoord F (r + 1) k M

theorem hasFDerivAt_sliceIntegrand (w : T.Space) (b : FiniteAdelicGL F (r + 1))
    (x : Points F (r + 1)) (g : ArchimedeanGL F (r + 1)) :
    HasFDerivAt (sliceIntegrand T w b x) (sliceDeriv T w b x (g : ArchimedeanMatrix F (r + 1)))
      (g : ArchimedeanMatrix F (r + 1)) := by
  set a := archPart F (r + 1) x with ha
  set f := finiteSmoothSlice F (r + 1) (finPart F (r + 1) x * b) (T.realization.ambient w)
  have h1 : HasFDerivAt (ArchimedeanGL.coordinateExtension F (r + 1) f)
      (fderiv ℝ (ArchimedeanGL.coordinateExtension F (r + 1) f)
        ((a : ArchimedeanMatrix F (r + 1)) * (g : ArchimedeanMatrix F (r + 1))))
      ((a : ArchimedeanMatrix F (r + 1)) * (g : ArchimedeanMatrix F (r + 1))) := by
    rw [← Units.val_mul]
    exact ((ArchimedeanGL.coordinateExtension_contDiffAt F (r + 1) f (a * g)).differentiableAt
      (by simp)).hasFDerivAt
  have h2 := h1.comp (g : ArchimedeanMatrix F (r + 1))
    ((hasFDerivAt_id (g : ArchimedeanMatrix F (r + 1))).const_mul (a : ArchimedeanMatrix F (r + 1)))
  refine h2.congr_fderiv ?_
  ext V
  have hV : (((a * g)⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) *
      ((a : ArchimedeanMatrix F (r + 1)) * V) =
      ((g⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) * V := by
    rw [mul_inv_rev, Units.val_mul, mul_assoc, ← mul_assoc ((a⁻¹ : ArchimedeanGL F (r + 1)) :
      ArchimedeanMatrix F (r + 1)), Units.inv_mul, one_mul]
  have hL : fderiv ℝ (ArchimedeanGL.coordinateExtension F (r + 1) f)
      ((a : ArchimedeanMatrix F (r + 1)) * (g : ArchimedeanMatrix F (r + 1)))
      ((a : ArchimedeanMatrix F (r + 1)) * V) =
      cuspFunction F T (lieDeriv T (((g⁻¹ : ArchimedeanGL F (r + 1)) :
        ArchimedeanMatrix F (r + 1)) * V) w) (x * adelicPoint F (r + 1) g b) := by
    rw [← Units.val_mul, fderiv_coordinateExtension_slice, hV, cuspFunction_mul_adelicPoint]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [hL, cuspFunction_lieDeriv_eq_sum, sliceDeriv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, sliceIntegrand_units, invCoord_apply,
    Ring.inverse_unit, mul_comm]

end Slice

section WhittakerIntegral

local instance regUnipotentLocallyCompact (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)

/-- The set-integral form of the Whittaker function at `(M, b)`, extended to all archimedean
matrices `M` through `sliceIntegrand`. -/
def archWhittakerExt (w : T.Space) (b : FiniteAdelicGL F (r + 1))
    (M : ArchimedeanMatrix F (r + 1)) : ℂ :=
  (quotientMassNormalizer F (Scheme F (r + 1)) (upperUnipotent F (r + 1))).toReal •
    ∫ n in LeftCosetSpace.fundamentalDomain
        (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
        (isDiscrete_rationalSubgroup F _ _),
      sliceIntegrand T w b (n : Points F (r + 1)) M *
        starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n) ∂Measure.haar

theorem archWhittakerExt_units (hψ : IsStandardAdditiveCharacter F ψ) (w : T.Space)
    (b : FiniteAdelicGL F (r + 1)) (g : ArchimedeanGL F (r + 1)) :
    archWhittakerExt T ψ w b (g : ArchimedeanMatrix F (r + 1)) =
      Unfolding.whittaker F r ψ (cuspFunction F T w) (adelicPoint F (r + 1) g b) :=
  (congrArg (fun z : ℂ =>
      (quotientMassNormalizer F (Scheme F (r + 1)) (upperUnipotent F (r + 1))).toReal • z)
    (integral_congr_ae (ae_of_all _ fun n =>
      congrArg (· * starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n))
        (sliceIntegrand_units T w b (n : Points F (r + 1)) g)))).trans
    (Unfolding.whittaker_eq_setIntegral F ψ hψ _ (Unfolding.continuous_cuspFunction F T w)
      (fun _ hk x => Unfolding.cuspFunction_rational_mul F T w hk x) _).symm

/-- The candidate derivative of `archWhittakerExt` at an invertible `M`. -/
def archWhittakerDeriv (w : T.Space) (b : FiniteAdelicGL F (r + 1))
    (M : ArchimedeanMatrix F (r + 1)) : ArchimedeanMatrix F (r + 1) →L[ℝ] ℂ :=
  ∑ k, archWhittakerExt T ψ (lieDeriv T (Module.finBasis ℝ (ArchimedeanMatrix F (r + 1)) k) w)
    b M • invCoord F (r + 1) k M

theorem hasFDerivAt_archWhittakerExt (hψ : IsStandardAdditiveCharacter F ψ) (w : T.Space)
    (b : FiniteAdelicGL F (r + 1)) (g₀ : ArchimedeanGL F (r + 1)) :
    HasFDerivAt (archWhittakerExt T ψ w b)
      (archWhittakerDeriv T ψ w b (g₀ : ArchimedeanMatrix F (r + 1)))
      (g₀ : ArchimedeanMatrix F (r + 1)) := by
  set e := Module.finBasis ℝ (ArchimedeanMatrix F (r + 1)) with he
  set D := LeftCosetSpace.fundamentalDomain
    (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
    (isDiscrete_rationalSubgroup F _ _) with hD
  set c := (quotientMassNormalizer F (Scheme F (r + 1)) (upperUnipotent F (r + 1))).toReal
    with hc
  set χ := genericCharacter F r ψ (fun _ => 1) with hχ
  set ν := (Measure.haar : Measure (unipotentAdelic F (r + 1))).restrict D with hν
  set d := detNorm F (r + 1) (adelicPoint F (r + 1) g₀ b) with hd
  have hd0 : 0 < d := Unfolding.detNorm_pos F (r + 1) _
  have hlo : 0 < d / 2 := by positivity
  have hBex := fun k => Unfolding.exists_bound_cuspFunction F T (lieDeriv T (e k) w)
    (lo := d / 2) (hi := 2 * d) hlo
  choose B hB using hBex
  obtain ⟨B₀, hB₀⟩ := Unfolding.exists_bound_cuspFunction F T w (lo := d / 2) (hi := 2 * d) hlo
  set U : Set (ArchimedeanGL F (r + 1)) :=
    {g | detNorm F (r + 1) (adelicPoint F (r + 1) g b) ∈ Set.Ioo (d / 2) (2 * d)} with hU
  have hUo : IsOpen U := isOpen_Ioo.preimage (continuous_detNorm_adelicPoint F (r + 1) b)
  have hg₀U : g₀ ∈ U := by
    show d ∈ Set.Ioo (d / 2) (2 * d)
    constructor <;> linarith
  set s : Set (ArchimedeanMatrix F (r + 1)) := (Units.val '' U) ∩
    {M | ∀ k, ‖invCoord F (r + 1) k M‖ <
      ‖invCoord F (r + 1) k (g₀ : ArchimedeanMatrix F (r + 1))‖ + 1} with hs
  have hs_nhds : s ∈ 𝓝 (g₀ : ArchimedeanMatrix F (r + 1)) := by
    refine Filter.inter_mem
      ((Units.isOpenEmbedding_val.isOpenMap U hUo).mem_nhds ⟨g₀, hg₀U, rfl⟩) ?_
    refine Filter.eventually_all.mpr fun k => ?_
    have hcont : ContinuousAt (invCoord F (r + 1) k) (g₀ : ArchimedeanMatrix F (r + 1)) :=
      (contDiffOn_invCoord F (r + 1) k (m := 0)).continuousOn.continuousAt
        (Units.isOpen.mem_nhds g₀.isUnit)
    exact hcont.norm.eventually_lt continuousAt_const (lt_add_one _)
  have hsU : ∀ M ∈ s, ∃ g : ArchimedeanGL F (r + 1), (g : ArchimedeanMatrix F (r + 1)) = M ∧
      g ∈ U ∧ ∀ k, ‖invCoord F (r + 1) k M‖ <
        ‖invCoord F (r + 1) k (g₀ : ArchimedeanMatrix F (r + 1))‖ + 1 := by
    rintro M ⟨⟨g, hg, rfl⟩, hk⟩
    exact ⟨g, rfl, hg, hk⟩
  have hχc : Continuous fun n : unipotentAdelic F (r + 1) => starRingEnd ℂ (χ n) :=
    Complex.continuous_conj.comp (Unfolding.continuous_genericCharacter F r ψ hψ.1 _)
  have hχn : ∀ n : unipotentAdelic F (r + 1), ‖starRingEnd ℂ (χ n)‖ = 1 := fun n =>
    (Complex.norm_conj _).trans (Unfolding.norm_genericCharacter F r ψ hψ.2.2.2 _ n)
  have hfin := Unfolding.haar_unipotentFundamentalDomain_lt_top F (r := r)
  have hband : ∀ g ∈ U, ∀ n : unipotentAdelic F (r + 1),
      d / 2 ≤ detNorm F (r + 1) ((n : Points F (r + 1)) * adelicPoint F (r + 1) g b) ∧
        detNorm F (r + 1) ((n : Points F (r + 1)) * adelicPoint F (r + 1) g b) ≤ 2 * d := by
    intro g hg n
    rw [Unfolding.detNorm_mul, Unfolding.detNorm_unipotent, one_mul]
    exact ⟨hg.1.le, hg.2.le⟩
  have hcontg : ∀ (v : T.Space) (g : ArchimedeanGL F (r + 1)),
      Continuous fun n : unipotentAdelic F (r + 1) =>
        sliceIntegrand T v b (n : Points F (r + 1)) (g : ArchimedeanMatrix F (r + 1)) *
          starRingEnd ℂ (χ n) := fun v g =>
    (((Unfolding.continuous_cuspFunction F T v).comp
      (continuous_subtype_val.mul continuous_const)).mul hχc).congr fun n =>
        congrArg (· * starRingEnd ℂ (χ n)) (sliceIntegrand_units T v b _ g).symm
  have hint : ∀ (v : T.Space) (C : ℝ), (∀ x : Points F (r + 1), d / 2 ≤ detNorm F (r + 1) x →
      detNorm F (r + 1) x ≤ 2 * d → ‖cuspFunction F T v x‖ ≤ C) → ∀ g ∈ U,
      Integrable (fun n : unipotentAdelic F (r + 1) =>
        sliceIntegrand T v b (n : Points F (r + 1)) (g : ArchimedeanMatrix F (r + 1)) *
          starRingEnd ℂ (χ n)) ν := by
    intro v C hC g hg
    refine IntegrableOn.of_bound hfin (hcontg v g).aestronglyMeasurable C
      (ae_of_all _ fun n => ?_)
    rw [norm_mul, hχn, mul_one, sliceIntegrand_units]
    exact hC _ (hband g hg n).1 (hband g hg n).2
  have hslice : ∀ k, ∀ g ∈ U, ∀ n : unipotentAdelic F (r + 1),
      ‖sliceIntegrand T (lieDeriv T (e k) w) b (n : Points F (r + 1))
        (g : ArchimedeanMatrix F (r + 1))‖ ≤ B k := by
    intro k g hg n
    rw [sliceIntegrand_units]
    exact hB k _ (hband g hg n).1 (hband g hg n).2
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun M (n : unipotentAdelic F (r + 1)) =>
      sliceIntegrand T w b (n : Points F (r + 1)) M * starRingEnd ℂ (χ n))
    (F' := fun M (n : unipotentAdelic F (r + 1)) =>
      ∑ k, (sliceIntegrand T (lieDeriv T (e k) w) b (n : Points F (r + 1)) M *
        starRingEnd ℂ (χ n)) • invCoord F (r + 1) k M)
    (bound := fun _ => ∑ k, B k *
      (‖invCoord F (r + 1) k (g₀ : ArchimedeanMatrix F (r + 1))‖ + 1))
    (x₀ := (g₀ : ArchimedeanMatrix F (r + 1))) hs_nhds
    (Filter.mem_of_superset hs_nhds fun M hM => by
      obtain ⟨g, rfl, -, -⟩ := hsU M hM
      exact (hcontg w g).aestronglyMeasurable)
    (hint w B₀ hB₀ g₀ hg₀U)
    (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (hcontg (lieDeriv T (e k) w) g₀).aestronglyMeasurable.smul_const _)
    (ae_of_all _ fun n M hM => by
      obtain ⟨g, rfl, hg, hk⟩ := hsU M hM
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_smul, norm_mul, hχn, mul_one]
      exact mul_le_mul (hslice k g hg n) (hk k).le (norm_nonneg _)
        ((norm_nonneg _).trans (hslice k g hg n)))
    (integrableOn_const hfin.ne)
    (ae_of_all _ fun n M hM => by
      obtain ⟨g, rfl, -, -⟩ := hsU M hM
      refine ((hasFDerivAt_sliceIntegrand T w b (n : Points F (r + 1)) g).mul_const
        (starRingEnd ℂ (χ n))).congr_fderiv ?_
      simp only [sliceDeriv, Finset.smul_sum, smul_smul]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm])
  refine (hmain.const_smul c).congr_fderiv ?_
  rw [integral_finsetSum _ fun k _ =>
    (hint (lieDeriv T (e k) w) (B k) (hB k) g₀ hg₀U).smul_const _]
  simp only [integral_smul_const, Finset.smul_sum, archWhittakerDeriv, archWhittakerExt,
    smul_assoc]
  rfl

/-- The extended Whittaker integral is smooth of every finite order on the invertible matrices,
for every vector. -/
theorem contDiffOn_archWhittakerExt_nat (hψ : IsStandardAdditiveCharacter F ψ)
    (b : FiniteAdelicGL F (r + 1)) (m : ℕ) :
    ∀ w : T.Space, ContDiffOn ℝ m (archWhittakerExt T ψ w b)
      {M : ArchimedeanMatrix F (r + 1) | IsUnit M} := by
  induction m with
  | zero =>
    intro w
    refine contDiffOn_zero.mpr fun M hM => ?_
    obtain ⟨g, rfl⟩ := hM
    exact (hasFDerivAt_archWhittakerExt T ψ hψ w b g).continuousAt.continuousWithinAt
  | succ m ih =>
    intro w
    rw [Nat.cast_add, Nat.cast_one]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen Units.isOpen).mpr ⟨?_, ?_, ?_⟩
    · rintro M ⟨g, rfl⟩
      exact (hasFDerivAt_archWhittakerExt T ψ hψ w b g).differentiableAt.differentiableWithinAt
    · intro h
      exact absurd h (WithTop.natCast_ne_top m)
    · refine ContDiffOn.congr (f := archWhittakerDeriv T ψ w b) ?_ fun M hM => ?_
      · exact ContDiffOn.sum fun k _ => (ih _).fun_smul (contDiffOn_invCoord F (r + 1) k)
      · obtain ⟨g, rfl⟩ := hM
        exact (hasFDerivAt_archWhittakerExt T ψ hψ w b g).fderiv

/-- The extended Whittaker integral is smooth on the invertible matrices. -/
theorem contDiffOn_archWhittakerExt (hψ : IsStandardAdditiveCharacter F ψ) (w : T.Space)
    (b : FiniteAdelicGL F (r + 1)) :
    ContDiffOn ℝ ∞ (archWhittakerExt T ψ w b) {M : ArchimedeanMatrix F (r + 1) | IsUnit M} :=
  contDiffOn_infty.mpr fun m => contDiffOn_archWhittakerExt_nat T ψ hψ b m w

/-- The integrand of `archWhittakerExt` at an invertible matrix is integrable. -/
theorem integrable_sliceIntegrand (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space)
    (b : FiniteAdelicGL F (r + 1)) (g : ArchimedeanGL F (r + 1)) :
    Integrable (fun n : unipotentAdelic F (r + 1) =>
        sliceIntegrand T v b (n : Points F (r + 1)) (g : ArchimedeanMatrix F (r + 1)) *
          starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n))
      ((Measure.haar : Measure (unipotentAdelic F (r + 1))).restrict
        (LeftCosetSpace.fundamentalDomain
          (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
          (isDiscrete_rationalSubgroup F _ _))) := by
  set d := detNorm F (r + 1) (adelicPoint F (r + 1) g b) with hd
  obtain ⟨B, hB⟩ := Unfolding.exists_bound_cuspFunction F T v (lo := d) (hi := d)
    (Unfolding.detNorm_pos F (r + 1) _)
  have h := Unfolding.integrableOn_whittakerIntegrand F ψ hψ (cuspFunction F T v)
    (Unfolding.continuous_cuspFunction F T v) (adelicPoint F (r + 1) g b) B fun u => by
      have e : detNorm F (r + 1) ((u : Points F (r + 1)) * adelicPoint F (r + 1) g b) = d := by
        rw [Unfolding.detNorm_mul, Unfolding.detNorm_unipotent, one_mul]
      exact hB _ e.ge e.le
  exact h.congr (ae_of_all _ fun n =>
    congrArg (· * starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n))
      (sliceIntegrand_units T v b (n : Points F (r + 1)) g).symm)

/-- At an invertible matrix, `archWhittakerExt` of `R(Z) w` is real-linear in `Z`. -/
theorem archWhittakerExt_lieDeriv_eq_sum (hψ : IsStandardAdditiveCharacter F ψ)
    (Z : ArchimedeanMatrix F (r + 1)) (w : T.Space) (b : FiniteAdelicGL F (r + 1))
    (g : ArchimedeanGL F (r + 1)) :
    archWhittakerExt T ψ (lieDeriv T Z w) b (g : ArchimedeanMatrix F (r + 1)) =
      ∑ k, (((Module.finBasis ℝ (ArchimedeanMatrix F (r + 1))).repr Z k : ℝ) : ℂ) *
        archWhittakerExt T ψ (lieDeriv T (Module.finBasis ℝ (ArchimedeanMatrix F (r + 1)) k) w)
          b (g : ArchimedeanMatrix F (r + 1)) := by
  have hpt : ∀ n : unipotentAdelic F (r + 1),
      sliceIntegrand T (lieDeriv T Z w) b (n : Points F (r + 1)) (g : ArchimedeanMatrix F (r + 1)) *
          starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n) =
        ∑ k, (((Module.finBasis ℝ (ArchimedeanMatrix F (r + 1))).repr Z k : ℝ) : ℂ) *
          (sliceIntegrand T (lieDeriv T (Module.finBasis ℝ (ArchimedeanMatrix F (r + 1)) k) w) b
            (n : Points F (r + 1)) (g : ArchimedeanMatrix F (r + 1)) *
              starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n)) := by
    intro n
    rw [sliceIntegrand_units, cuspFunction_lieDeriv_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sliceIntegrand_units, mul_assoc]
  unfold archWhittakerExt
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun k _ =>
    (integrable_sliceIntegrand T ψ hψ _ b g).const_mul _, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, mul_smul_comm]

/-- The derivative of `archWhittakerExt` at `g` in the direction `g Z` is `archWhittakerExt` of
`R(Z) w`. -/
theorem fderiv_archWhittakerExt_mul (hψ : IsStandardAdditiveCharacter F ψ) (w : T.Space)
    (b : FiniteAdelicGL F (r + 1)) (g : ArchimedeanGL F (r + 1))
    (Z : ArchimedeanMatrix F (r + 1)) :
    fderiv ℝ (archWhittakerExt T ψ w b) (g : ArchimedeanMatrix F (r + 1))
        ((g : ArchimedeanMatrix F (r + 1)) * Z) =
      archWhittakerExt T ψ (lieDeriv T Z w) b (g : ArchimedeanMatrix F (r + 1)) := by
  rw [(hasFDerivAt_archWhittakerExt T ψ hψ w b g).fderiv, archWhittakerDeriv, _root_.sum_apply,
    archWhittakerExt_lieDeriv_eq_sum T ψ hψ]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [_root_.smul_apply, invCoord_apply, Ring.inverse_unit, ← mul_assoc, Units.inv_mul, one_mul,
    smul_eq_mul, mul_comm]

end WhittakerIntegral

section Growth

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

/-- **Global determinant bound.** There is `β` such that every Whittaker function of a vector of
`T` is bounded by a constant times `|det g|^β`. -/
theorem exists_norm_cuspWhittaker_le :
    ∃ β : ℝ, ∀ ψ : AddChar (Adeles F) ℂ, IsStandardAdditiveCharacter F ψ → ∀ v : T.Space,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Points F (r + 1),
        ‖cuspWhittaker F T ψ v g‖ ≤ C * detNorm F (r + 1) g ^ β := by
  obtain ⟨β, hβ⟩ := CuspCentralBound.exists_norm_cuspFunction_le F T
  refine ⟨β, fun ψ hψ v => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hβ v
  refine ⟨C, hC0, fun g => ?_⟩
  refine Unfolding.norm_whittaker_le F ψ hψ (cuspFunction F T v) g _ fun u => ?_
  have h := hC ((u : Points F (r + 1)) * g)
  rwa [Unfolding.detNorm_mul, Unfolding.detNorm_unipotent, one_mul] at h

end Growth

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerRegularity
