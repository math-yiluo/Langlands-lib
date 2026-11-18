import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientStatement
import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientJointFinite
import Langlands.Automorphic.CuspidalTranslatedBandIntegrability
import Langlands.Global.ArchimedeanOrbitDerivativeInterchange

/-! # Smooth actual determinant-band Hilbert orbit coefficients

For a cuspidal operator realization and an arbitrary band `L²` vector `w`, the scalar
coefficient `g ↦ ∫ ⟪w(q), f(q · g)⟫` is smooth on the archimedean group and its real
directional derivatives are the coefficients of the Lie derivatives of `f`; hence the
coefficient map commutes with the genuine enveloping actions. Joint finiteness comes
from `CuspidalHilbertOrbitCoefficientJointFinite`, and the final theorem proves
`CuspidalHilbertOrbitCoefficientStatement`. -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology Metric
open scoped Classical NNReal ENNReal ContDiff Manifold Matrix.Norms.Operator CategoryTheory.MonObj

namespace Langlands.Automorphic.CuspidalHilbertOrbitCoefficientProof

open Langlands.Global ContinuousRationalFunctions OperatorDeterminantSlice ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance proofRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance proofContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance proofSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance proofFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance proofStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance proofIsAffine :
    _root_.AlgebraicGeometry.IsAffine (matrixGroupScheme F n).X.left :=
  Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance proofSmooth :
    _root_.AlgebraicGeometry.Smooth (matrixGroupScheme F n).X.hom :=
  Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (S : OperatorRealization F n)

local instance proofSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-! ### Suprema of translates over a compact set -/

section CompactSup

/-- Translating a realized quotient function is jointly continuous in the point and
the adelic translation parameter. -/
theorem continuous_toQuotient_translate₂ (h : S.Space) :
    Continuous (fun p : Quotient F n × AdelicGL F n =>
      toQuotient F n S h (translate F n p.2 p.1)) := by
  rw [← ((LeftCosetSpace.isOpenQuotientMap_mk _).prodMap
    IsOpenQuotientMap.id).continuous_comp_iff]
  have heq : ((fun p : Quotient F n × AdelicGL F n =>
      toQuotient F n S h (translate F n p.2 p.1)) ∘
      Prod.map (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F (matrixGroupScheme F n)))
        id) = fun p => evaluate F n (S.toContinuous h)
          (GeneralLinearGroupPoints.adelicHomeomorph F n p.1 * p.2) := by
    funext p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
      ← point_adelicHomeomorph, translate_point, toQuotient_point]
  rw [heq]
  exact (continuous_evaluate F n _).comp
    (((GeneralLinearGroupPoints.adelicHomeomorph F n).continuous.comp continuous_fst).mul
      continuous_snd)

theorem continuous_norm_translate (h : S.Space) (q : Quotient F n) :
    Continuous (fun c : AdelicGL F n => ‖toQuotient F n S h (translate F n c q)‖) := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  simp only [translate_point, toQuotient_point]
  exact ((continuous_evaluate F n _).comp (continuous_const.mul continuous_id)).norm

/-- The largest value of the translates of a realized vector over a set `Γ`. -/
def compactSup (Γ : Set (AdelicGL F n)) (h : S.Space) (q : Quotient F n) : ℝ :=
  sSup ((fun c => ‖toQuotient F n S h (translate F n c q)‖) '' Γ)

theorem continuous_compactSup {Γ : Set (AdelicGL F n)} (hΓ : IsCompact Γ) (h : S.Space) :
    Continuous (compactSup S Γ h) :=
  hΓ.continuous_sSup (continuous_norm.comp (continuous_toQuotient_translate₂ S h))

theorem norm_le_compactSup {Γ : Set (AdelicGL F n)} (hΓ : IsCompact Γ) (h : S.Space)
    (q : Quotient F n) {c : AdelicGL F n} (hc : c ∈ Γ) :
    ‖toQuotient F n S h (translate F n c q)‖ ≤ compactSup S Γ h q :=
  le_csSup (hΓ.bddAbove_image (continuous_norm_translate S h q).continuousOn)
    (Set.mem_image_of_mem _ hc)

theorem exists_compactSup_eq {Γ : Set (AdelicGL F n)} (hΓ : IsCompact Γ) (hne : Γ.Nonempty)
    (h : S.Space) (x : AdelicGL F n) :
    ∃ c ∈ Γ, compactSup S Γ h (point F n x) =
      ‖evaluate F n (S.toContinuous h) (x * c)‖ := by
  obtain ⟨c, hc, hceq⟩ := (hΓ.image (continuous_norm_translate S h (point F n x))).sSup_mem
    (hne.image _)
  refine ⟨c, hc, ?_⟩
  rw [compactSup, ← hceq]
  simp only [translate_point, toQuotient_point]

/-- The compact supremum function of a cuspidal vector is square integrable on the band. -/
theorem memLp_compactSup [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    {Γ : Set (AdelicGL F n)} (hΓ : IsCompact Γ) (hne : Γ.Nonempty) (h : S.Space) :
    MemLp (compactSup S Γ h) 2 ((quotientHaarMeasure F n).restrict (band F n)) := by
  let : MeasurableSpace (AdelicGL F n) := borel _
  have : BorelSpace (AdelicGL F n) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfin⟩ := S.exists_band_cover_uniform hS (lo := 1) (hi := 2) one_pos
    Γ hΓ
  refine memLp_band_of_continuous F n _ (continuous_compactSup S hΓ h) t ht
    (fun x hx => hcover x hx.1 hx.2) ?_
  refine hfin (matrixHaarMeasure F n) h _ fun x => ?_
  obtain ⟨c, hc, heq⟩ := exists_compactSup_eq S hΓ hne h x
  exact ⟨c, hc, le_of_eq (by rw [heq, enorm_norm])⟩

end CompactSup

/-! ### Matrix coordinates -/

section Coordinates

variable (F n) in
/-- The open set of invertible archimedean matrices. -/
def unitSet : Set (ArchimedeanMatrix F n) :=
  Set.range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n)

theorem isOpen_unitSet : IsOpen (unitSet F n) := by
  have h := (unitsChart F n).open_target
  rwa [unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_target] at h

variable (F n) in
/-- The infinite group element of an invertible matrix, through the units chart. -/
def unitPoint (y : ArchimedeanMatrix F n) : InfiniteAdelicGL F n :=
  (archimedeanGLCoordinates F n).symm ((unitsChart F n).symm y)

theorem unitPoint_val (v : ArchimedeanGL F n) :
    unitPoint F n (v : ArchimedeanMatrix F n) = (archimedeanGLCoordinates F n).symm v := by
  simp only [unitPoint, unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

theorem continuousOn_unitPoint : ContinuousOn (unitPoint F n) (unitSet F n) := by
  have h := (unitsChart F n).continuousOn_symm
  rw [unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_target] at h
  exact (archimedeanGLCoordinates F n).symm.continuous.comp_continuousOn h

variable (F n) in
/-- The adelic translation parameter of an invertible archimedean matrix. -/
abbrev adelicPoint (y : ArchimedeanMatrix F n) : AdelicGL F n :=
  AdelicGL.ofInfinite F n (unitPoint F n y)

theorem continuousOn_adelicPoint : ContinuousOn (adelicPoint F n) (unitSet F n) :=
  (map_continuous (AdelicGL.ofInfinite F n)).comp_continuousOn continuousOn_unitPoint

/-- A translated realized vector, evaluated at a represented point, is the archimedean
coordinate expression of a smooth slice. -/
theorem toQuotient_translate_unit (h : S.Space) (x : AdelicGL F n) (v : ArchimedeanGL F n) :
    toQuotient F n S h (translate F n (adelicPoint F n (v : ArchimedeanMatrix F n))
        (point F n x)) =
      coordinateExtension F n (finiteSmoothSlice F n (AdelicGL.finite F n x) (S.ambient h))
        ((archimedeanGLCoordinates F n (AdelicGL.infinite F n x) : ArchimedeanMatrix F n) *
          (v : ArchimedeanMatrix F n)) := by
  rw [adelicPoint, unitPoint_val, translate_point, toQuotient_point,
    OperatorRealization.mul_ofInfinite_eq_pair, S.evaluate_toContinuous,
    ← finiteSmoothSlice_apply, ← Units.val_mul, coordinateExtension_apply,
    map_mul (archimedeanGLCoordinates F n).symm, ContinuousMulEquiv.symm_apply_apply]

/-- A real Lie derivative of a realized vector, evaluated at a translated point. -/
theorem toQuotient_lieOperator_translate_unit (Z : RealLieAlgebra F n) (h : S.Space)
    (x : AdelicGL F n) (v : ArchimedeanGL F n) :
    toQuotient F n S (S.lieOperator Z h)
        (translate F n (adelicPoint F n (v : ArchimedeanMatrix F n)) (point F n x)) =
      fderiv ℝ (coordinateExtension F n
          (finiteSmoothSlice F n (AdelicGL.finite F n x) (S.ambient h)))
        ((archimedeanGLCoordinates F n (AdelicGL.infinite F n x) : ArchimedeanMatrix F n) *
          (v : ArchimedeanMatrix F n))
        (((archimedeanGLCoordinates F n (AdelicGL.infinite F n x) : ArchimedeanMatrix F n) *
          (v : ArchimedeanMatrix F n)) * realLieAlgebraToMatrix F n Z) := by
  have hmul : (archimedeanGLCoordinates F n (AdelicGL.infinite F n x *
      (archimedeanGLCoordinates F n).symm v) : ArchimedeanMatrix F n) =
      (archimedeanGLCoordinates F n (AdelicGL.infinite F n x) : ArchimedeanMatrix F n) *
        (v : ArchimedeanMatrix F n) := by
    rw [map_mul (archimedeanGLCoordinates F n) (AdelicGL.infinite F n x),
      ContinuousMulEquiv.apply_symm_apply, Units.val_mul]
  rw [adelicPoint, unitPoint_val, translate_point, toQuotient_point,
    OperatorRealization.mul_ofInfinite_eq_pair, S.evaluate_lieOperator_pair,
    smoothDifferential_apply]
  simp only [hmul]

/-- The Lie derivative in a matrix direction is the basis combination of the Lie
derivatives in the basis directions, pointwise on the quotient. -/
theorem toQuotient_lieOperator_eq_sum (Z : ArchimedeanMatrix F n) (h : S.Space)
    (p : Quotient F n) :
    toQuotient F n S (S.lieOperator ((realLieAlgebraToMatrix F n).symm Z) h) p =
      ∑ k, ((lieBasis F n).repr Z k : ℂ) *
        toQuotient F n S (S.lieOperator (lieDirection F n k) h) p := by
  obtain ⟨x, rfl⟩ := point_surjective F n p
  simp only [toQuotient_point]
  rw [← AdelicGL.pair_projections F n x]
  simp only [S.evaluate_lieOperator_pair]
  exact smoothDifferential_val_eq_sum _ Z _

end Coordinates

/-! ### Basis coordinates of `y⁻¹ Y` -/

section CoordFunctional

variable (F n) in
/-- The continuous linear map `a ↦ (Y ↦ k-th basis coordinate of a * Y)`. -/
def coordMap (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n))) :
    ArchimedeanMatrix F n →L[ℝ] ArchimedeanMatrix F n →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (ArchimedeanMatrix F n) (ArchimedeanMatrix F n) ℝ
    (LinearMap.toContinuousLinearMap ((lieBasis F n).coord k))).comp
    (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix F n))

variable (F n) in
/-- The `k`-th basis coordinate of `y⁻¹ Y`, as a real functional of `Y`. -/
def coordFunctional (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (y : ArchimedeanMatrix F n) : ArchimedeanMatrix F n →L[ℝ] ℝ :=
  coordMap F n k (Ring.inverse y)

theorem coordFunctional_apply (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (y Y : ArchimedeanMatrix F n) :
    coordFunctional F n k y Y = (lieBasis F n).coord k (Ring.inverse y * Y) := rfl

theorem contDiffOn_ringInverse (m : WithTop ℕ∞) :
    ContDiffOn ℝ m (Ring.inverse : ArchimedeanMatrix F n → ArchimedeanMatrix F n)
      (unitSet F n) := by
  rintro _ ⟨v, rfl⟩
  exact (contDiffAt_ringInverse ℝ v).contDiffWithinAt

theorem contDiffOn_coordFunctional (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (m : WithTop ℕ∞) :
    ContDiffOn ℝ m (coordFunctional F n k) (unitSet F n) :=
  (coordMap F n k).contDiff.comp_contDiffOn (contDiffOn_ringInverse m)

theorem coordFunctional_unit_mul (k : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)))
    (v : ArchimedeanGL F n) (Z : ArchimedeanMatrix F n) :
    coordFunctional F n k (v : ArchimedeanMatrix F n) ((v : ArchimedeanMatrix F n) * Z) =
      (lieBasis F n).repr Z k := by
  rw [coordFunctional_apply, Ring.inverse_unit, Units.inv_mul_cancel_left,
    Module.Basis.coord_apply]

theorem smulRightL_eq (c : ArchimedeanMatrix F n →L[ℝ] ℝ) (z : ℂ) :
    ContinuousLinearMap.smulRightL ℝ (ArchimedeanMatrix F n) ℂ c z = c.smulRight z := by
  ext Y
  simp only [ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply]

end CoordFunctional

/-! ### Differentiation under the integral -/

section Derivative

variable [CompactSpace (AdeleQuotient F)]
  (w : Lp ℂ 2 ((quotientHaarMeasure F n).restrict (band F n)))

/-- The coefficient at an archimedean group parameter. -/
def orbitCoefficient (h : S.Space) (g : InfiniteAdelicGL F n) : ℂ :=
  ∫ q, Inner.inner ℂ (w q) (toQuotient F n S h (translate F n (AdelicGL.ofInfinite F n g) q))
    ∂((quotientHaarMeasure F n).restrict (band F n))

/-- The coefficient integrand at a matrix parameter. -/
def matrixIntegrand (h : S.Space) (y : ArchimedeanMatrix F n) (q : Quotient F n) : ℂ :=
  Inner.inner ℂ (w q) (toQuotient F n S h (translate F n (adelicPoint F n y) q))

/-- The coefficient as a function of a matrix parameter. -/
def matrixCoefficient (h : S.Space) (y : ArchimedeanMatrix F n) : ℂ :=
  ∫ q, matrixIntegrand S w h y q ∂((quotientHaarMeasure F n).restrict (band F n))

omit [CompactSpace (AdeleQuotient F)] in
theorem matrixCoefficient_val (h : S.Space) (v : ArchimedeanGL F n) :
    matrixCoefficient S w h (v : ArchimedeanMatrix F n) =
      orbitCoefficient S w h ((archimedeanGLCoordinates F n).symm v) := by
  simp only [matrixCoefficient, matrixIntegrand, adelicPoint, unitPoint_val, orbitCoefficient]

theorem integrable_matrixIntegrand (hS : S.IsCuspidal) (h : S.Space)
    (y : ArchimedeanMatrix F n) :
    Integrable (matrixIntegrand S w h y) ((quotientHaarMeasure F n).restrict (band F n)) :=
  integrable_inner_translate_of_cuspidal S hS (adelicPoint F n y) h w

/-- The candidate derivative of the matrix integrand. -/
def integrandDeriv (h : S.Space) (y : ArchimedeanMatrix F n) (q : Quotient F n) :
    ArchimedeanMatrix F n →L[ℝ] ℂ :=
  ∑ k, (coordFunctional F n k y).smulRight
    (matrixIntegrand S w (S.lieOperator (lieDirection F n k) h) y q)

/-- The candidate derivative of the matrix coefficient. -/
def matrixDeriv (h : S.Space) (y : ArchimedeanMatrix F n) : ArchimedeanMatrix F n →L[ℝ] ℂ :=
  ∑ k, (coordFunctional F n k y).smulRight
    (matrixCoefficient S w (S.lieOperator (lieDirection F n k) h) y)

omit [CompactSpace (AdeleQuotient F)] in
theorem matrixDeriv_unit_mul (h : S.Space) (v : ArchimedeanGL F n) (Z : ArchimedeanMatrix F n) :
    matrixDeriv S w h (v : ArchimedeanMatrix F n) ((v : ArchimedeanMatrix F n) * Z) =
      ∑ k, ((lieBasis F n).repr Z k : ℂ) *
        matrixCoefficient S w (S.lieOperator (lieDirection F n k) h)
          (v : ArchimedeanMatrix F n) := by
  simp only [matrixDeriv, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, coordFunctional_unit_mul, Complex.real_smul]

omit [CompactSpace (AdeleQuotient F)] in
/-- Pointwise derivative of the integrand at an invertible matrix. -/
theorem hasFDerivAt_matrixIntegrand (h : S.Space) {y : ArchimedeanMatrix F n}
    (hy : y ∈ unitSet F n) (q : Quotient F n) :
    HasFDerivAt (fun y' => matrixIntegrand S w h y' q) (integrandDeriv S w h y q) y := by
  obtain ⟨x, rfl⟩ := point_surjective F n q
  obtain ⟨v, rfl⟩ := hy
  set s := finiteSmoothSlice F n (AdelicGL.finite F n x) (S.ambient h) with hs_def
  set A : ArchimedeanMatrix F n :=
    (archimedeanGLCoordinates F n (AdelicGL.infinite F n x) : ArchimedeanMatrix F n) with hA_def
  set d : ℂ := (starRingEnd ℂ) (w (point F n x)) with hd_def
  have hev : (fun y' => matrixIntegrand S w h y' (point F n x)) =ᶠ[𝓝 (v : ArchimedeanMatrix F n)]
      fun y' => d * coordinateExtension F n s (A * y') := by
    filter_upwards [isOpen_unitSet.mem_nhds ⟨v, rfl⟩] with y' hy'
    obtain ⟨v', rfl⟩ := hy'
    rw [matrixIntegrand, toQuotient_translate_unit, RCLike.inner_apply']
  have hlin : HasFDerivAt (fun y' : ArchimedeanMatrix F n => A * y')
      (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix F n) A) (v : ArchimedeanMatrix F n) :=
    (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix F n) A).hasFDerivAt
  have hdiff : DifferentiableAt ℝ (coordinateExtension F n s)
      (A * (v : ArchimedeanMatrix F n)) := by
    have := (coordinateExtension_contDiffAt F n s
      (archimedeanGLCoordinates F n (AdelicGL.infinite F n x) * v)).differentiableAt (by simp)
    simpa only [Units.val_mul] using this
  have hcomp := (hdiff.hasFDerivAt.comp (v : ArchimedeanMatrix F n) hlin).const_mul d
  refine (hcomp.congr_of_eventuallyEq hev).congr_fderiv ?_
  ext Y
  have hZ : A * Y = (A * (v : ArchimedeanMatrix F n)) *
      (Ring.inverse (v : ArchimedeanMatrix F n) * Y) := by
    rw [Ring.inverse_unit, mul_assoc, Units.mul_inv_cancel_left]
  have hT := toQuotient_lieOperator_translate_unit S
    ((realLieAlgebraToMatrix F n).symm (Ring.inverse (v : ArchimedeanMatrix F n) * Y)) h x v
  rw [LinearEquiv.apply_symm_apply, toQuotient_lieOperator_eq_sum, ← hs_def, ← hA_def] at hT
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul, integrandDeriv, FunLike.coe_sum,
    Finset.sum_apply, ContinuousLinearMap.smulRight_apply, coordFunctional_apply,
    matrixIntegrand, RCLike.inner_apply']
  have hL := (DFunLike.congr_arg (fderiv ℝ (coordinateExtension F n s)
    (A * (v : ArchimedeanMatrix F n))) hZ).trans hT.symm
  simp only [hL, Finset.mul_sum, Module.Basis.coord_apply, Complex.real_smul]
  exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _

omit [CompactSpace (AdeleQuotient F)] in
theorem norm_integrandDeriv_le (h : S.Space) {s : Set (ArchimedeanMatrix F n)}
    (hΓ : IsCompact (adelicPoint F n '' s))
    (Cb : Fin (Module.finrank ℝ (ArchimedeanMatrix F n)) → ℝ)
    (hCb : ∀ k, ∀ y ∈ s, ‖coordFunctional F n k y‖ ≤ Cb k) {y : ArchimedeanMatrix F n}
    (hy : y ∈ s) (q : Quotient F n) :
    ‖integrandDeriv S w h y q‖ ≤ ∑ k, Cb k * (‖w q‖ *
      compactSup S (adelicPoint F n '' s) (S.lieOperator (lieDirection F n k) h) q) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul (hCb k y hy) ((norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_le_compactSup S hΓ _ q ⟨y, hy, rfl⟩) (norm_nonneg _)))
    (norm_nonneg _) ((norm_nonneg _).trans (hCb k y hy))

theorem integrable_smulRight_matrixIntegrand (hS : S.IsCuspidal) (h : S.Space)
    (c : ArchimedeanMatrix F n →L[ℝ] ℝ) (y : ArchimedeanMatrix F n) :
    Integrable (fun q => c.smulRight (matrixIntegrand S w h y q))
      ((quotientHaarMeasure F n).restrict (band F n)) := by
  simpa only [smulRightL_eq] using
    (ContinuousLinearMap.smulRightL ℝ (ArchimedeanMatrix F n) ℂ c).integrable_comp
      (integrable_matrixIntegrand S w hS h y)

theorem integral_integrandDeriv (hS : S.IsCuspidal) (h : S.Space)
    (y : ArchimedeanMatrix F n) :
    ∫ q, integrandDeriv S w h y q ∂((quotientHaarMeasure F n).restrict (band F n)) =
      matrixDeriv S w h y := by
  have hfun : (fun q => integrandDeriv S w h y q) = fun q => ∑ k,
      (coordFunctional F n k y).smulRight
        (matrixIntegrand S w (S.lieOperator (lieDirection F n k) h) y q) := by
    funext q
    simp only [integrandDeriv]
  rw [hfun, integral_finsetSum _ fun k _ => integrable_smulRight_matrixIntegrand S w hS _ _ y]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := (ContinuousLinearMap.smulRightL ℝ (ArchimedeanMatrix F n) ℂ
    (coordFunctional F n k y)).integral_comp_comm
      (integrable_matrixIntegrand S w hS (S.lieOperator (lieDirection F n k) h) y)
  simpa only [smulRightL_eq, matrixCoefficient] using this

theorem aestronglyMeasurable_integrandDeriv (hS : S.IsCuspidal) (h : S.Space)
    (y : ArchimedeanMatrix F n) :
    AEStronglyMeasurable (integrandDeriv S w h y)
      ((quotientHaarMeasure F n).restrict (band F n)) := by
  have hfun : integrandDeriv S w h y = fun q => ∑ k,
      (coordFunctional F n k y).smulRight
        (matrixIntegrand S w (S.lieOperator (lieDirection F n k) h) y q) := by
    funext q
    simp only [integrandDeriv]
  rw [hfun]
  exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
    (integrable_smulRight_matrixIntegrand S w hS _ _ y).aestronglyMeasurable

/-- Differentiation under the integral: the matrix coefficient has derivative
`matrixDeriv` at every invertible matrix. -/
theorem hasFDerivAt_matrixCoefficient (hS : S.IsCuspidal) (h : S.Space)
    {y₀ : ArchimedeanMatrix F n} (hy₀ : y₀ ∈ unitSet F n) :
    HasFDerivAt (matrixCoefficient S w h) (matrixDeriv S w h y₀) y₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_unitSet y₀ hy₀
  set s := closedBall y₀ (ε / 2) with hs_def
  have hsU : s ⊆ unitSet F n := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hs : s ∈ 𝓝 y₀ := closedBall_mem_nhds y₀ (half_pos hε)
  have hsc : IsCompact s := isCompact_closedBall y₀ (ε / 2)
  have hΓ : IsCompact (adelicPoint F n '' s) :=
    hsc.image_of_continuousOn (continuousOn_adelicPoint.mono hsU)
  have hΓne : (adelicPoint F n '' s).Nonempty :=
    ⟨_, y₀, mem_closedBall_self (half_pos hε).le, rfl⟩
  have hcf : ∀ k, ∃ C, ∀ y ∈ s, ‖coordFunctional F n k y‖ ≤ C := fun k =>
    hsc.exists_bound_of_continuousOn
      ((contDiffOn_coordFunctional (F := F) (n := n) k 0).continuousOn.mono hsU)
  choose Cb hCb using hcf
  have hint : Integrable (fun q => ∑ k, Cb k * (‖w q‖ *
      compactSup S (adelicPoint F n '' s) (S.lieOperator (lieDirection F n k) h) q))
      ((quotientHaarMeasure F n).restrict (band F n)) :=
    integrable_finsetSum _ fun k _ =>
      ((Lp.memLp w).norm.integrable_mul (memLp_compactSup S hS hΓ hΓne _)).const_mul (Cb k)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y q => matrixIntegrand S w h y q) (F' := fun y q => integrandDeriv S w h y q)
    hs (Eventually.of_forall fun y => (integrable_matrixIntegrand S w hS h y).aestronglyMeasurable)
    (integrable_matrixIntegrand S w hS h y₀)
    (aestronglyMeasurable_integrandDeriv S w hS h y₀)
    (ae_of_all _ fun q y hy => norm_integrandDeriv_le S w h hΓ Cb hCb hy q)
    hint
    (ae_of_all _ fun q y hy => hasFDerivAt_matrixIntegrand S w h (hsU hy) q)
  rw [integral_integrandDeriv S w hS h y₀] at key
  exact key

end Derivative

/-! ### Smoothness -/

section Smoothness

variable [CompactSpace (AdeleQuotient F)]
  (w : Lp ℂ 2 ((quotientHaarMeasure F n).restrict (band F n)))

/-- Every finite order of differentiability, by induction using the first-order formula. -/
theorem contDiffOn_matrixCoefficient (hS : S.IsCuspidal) (m : ℕ) :
    ∀ h : S.Space, ContDiffOn ℝ m (matrixCoefficient S w h) (unitSet F n) := by
  induction m with
  | zero =>
    intro h
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun y hy =>
      (hasFDerivAt_matrixCoefficient S w hS h hy).continuousAt.continuousWithinAt
  | succ m ih =>
    intro h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_unitSet]
    refine ⟨fun y hy =>
      (hasFDerivAt_matrixCoefficient S w hS h hy).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have hcongr : ∀ y ∈ unitSet F n,
        fderiv ℝ (matrixCoefficient S w h) y = matrixDeriv S w h y :=
      fun y hy => (hasFDerivAt_matrixCoefficient S w hS h hy).fderiv
    refine ContDiffOn.congr ?_ hcongr
    have hfun : matrixDeriv S w h = fun y => ∑ k, (coordFunctional F n k y).smulRight
          (matrixCoefficient S w (S.lieOperator (lieDirection F n k) h) y) := by
      funext y
      simp only [matrixDeriv]
    rw [hfun]
    exact ContDiffOn.sum fun k _ => (contDiffOn_coordFunctional k m).smulRight (ih _)

theorem contDiffOn_infty_matrixCoefficient (hS : S.IsCuspidal) (h : S.Space) :
    ContDiffOn ℝ ∞ (matrixCoefficient S w h) (unitSet F n) :=
  contDiffOn_infty.mpr fun m => contDiffOn_matrixCoefficient S w hS m h

/-- The orbit coefficient is a smooth function on the archimedean group. -/
theorem orbitCoefficient_mem (hS : S.IsCuspidal) (h : S.Space) :
    orbitCoefficient S w h ∈ smoothFunctions F n := by
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞ _
  intro v
  have hc : ContDiffAt ℝ ∞ (matrixCoefficient S w h) (v : ArchimedeanMatrix F n) :=
    (contDiffOn_infty_matrixCoefficient S w hS h).contDiffAt
      (isOpen_unitSet.mem_nhds ⟨v, rfl⟩)
  have hcomp := hc.comp_contMDiffAt (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) v)
  simpa only [Function.comp_def, matrixCoefficient_val] using hcomp

end Smoothness

/-! ### The coefficient map and its covariance -/

section Covariance

variable [CompactSpace (AdeleQuotient F)]
  (w : Lp ℂ 2 ((quotientHaarMeasure F n).restrict (band F n)))

theorem integrable_orbitIntegrand (hS : S.IsCuspidal) (h : S.Space) (g : InfiniteAdelicGL F n) :
    Integrable (fun q => Inner.inner ℂ (w q)
      (toQuotient F n S h (translate F n (AdelicGL.ofInfinite F n g) q)))
      ((quotientHaarMeasure F n).restrict (band F n)) :=
  integrable_inner_translate_of_cuspidal S hS (AdelicGL.ofInfinite F n g) h w

/-- The smooth orbit coefficients, as a complex-linear map. -/
def coefficientMap (hS : S.IsCuspidal) : S.Space →ₗ[ℂ] SmoothFunctions F n where
  toFun h := ⟨orbitCoefficient S w h, orbitCoefficient_mem S w hS h⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    change orbitCoefficient S w (f + h) g = orbitCoefficient S w f g + orbitCoefficient S w h g
    simp only [orbitCoefficient, map_add, ContinuousMap.add_apply, inner_add_right]
    exact integral_add (integrable_orbitIntegrand S w hS f g)
      (integrable_orbitIntegrand S w hS h g)
  map_smul' c f := by
    apply Subtype.ext
    funext g
    change orbitCoefficient S w (c • f) g = c * orbitCoefficient S w f g
    simp only [orbitCoefficient, map_smul, ContinuousMap.smul_apply, inner_smul_right]
    exact integral_const_mul c _

theorem coefficientMap_val (hS : S.IsCuspidal) (h : S.Space) (g : InfiniteAdelicGL F n) :
    (coefficientMap S w hS h).val g = orbitCoefficient S w h g := rfl

theorem matrixCoefficient_lieOperator_eq_sum (hS : S.IsCuspidal) (Z : ArchimedeanMatrix F n)
    (h : S.Space) (y : ArchimedeanMatrix F n) :
    matrixCoefficient S w (S.lieOperator ((realLieAlgebraToMatrix F n).symm Z) h) y =
      ∑ k, ((lieBasis F n).repr Z k : ℂ) *
        matrixCoefficient S w (S.lieOperator (lieDirection F n k) h) y := by
  have hfun : matrixIntegrand S w (S.lieOperator ((realLieAlgebraToMatrix F n).symm Z) h) y =
      fun q => ∑ k, ((lieBasis F n).repr Z k : ℂ) *
        matrixIntegrand S w (S.lieOperator (lieDirection F n k) h) y q := by
    funext q
    simp only [matrixIntegrand, toQuotient_lieOperator_eq_sum, RCLike.inner_apply',
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  simp only [matrixCoefficient]
  rw [hfun, integral_finsetSum _ fun k _ =>
    (integrable_matrixIntegrand S w hS _ y).const_mul _]
  simp only [integral_const_mul]

/-- The first-order covariance: real Lie derivatives of vectors correspond to
smooth real differentials of their coefficients. -/
theorem coefficientMap_lieOperator (hS : S.IsCuspidal) (X : RealLieAlgebra F n) (h : S.Space) :
    coefficientMap S w hS (S.lieOperator X h) =
      smoothDifferential F n X (coefficientMap S w hS h) := by
  apply Subtype.ext
  funext g
  have hext : ∀ v : ArchimedeanGL F n, matrixCoefficient S w h (v : ArchimedeanMatrix F n) =
      (coefficientMap S w hS h).val ((archimedeanGLCoordinates F n).symm v) :=
    fun v => matrixCoefficient_val S w h v
  set v := archimedeanGLCoordinates F n g with hv_def
  set M := realLieAlgebraToMatrix F n X with hM_def
  have e1 := smoothDifferential_eq_of_extension F n X (coefficientMap S w hS h)
    (matrixCoefficient S w h) hext g
  have e2 := (hasFDerivAt_matrixCoefficient S w hS h
    (y₀ := (v : ArchimedeanMatrix F n)) ⟨v, rfl⟩).fderiv
  have e3 := DFunLike.congr_fun e2 ((v : ArchimedeanMatrix F n) * M)
  have e4 := matrixDeriv_unit_mul S w h v M
  have e5 := matrixCoefficient_lieOperator_eq_sum S w hS M h (v : ArchimedeanMatrix F n)
  have hX : (realLieAlgebraToMatrix F n).symm M = X :=
    (realLieAlgebraToMatrix F n).symm_apply_apply X
  simp only [hX] at e5
  have hval := matrixCoefficient_val S w (S.lieOperator X h) v
  have hg : (archimedeanGLCoordinates F n).symm v = g :=
    ContinuousMulEquiv.symm_apply_apply _ g
  simp only [hg] at hval
  exact (coefficientMap_val S w hS (S.lieOperator X h) g).trans
    (hval.symm.trans (e5.trans (e4.symm.trans (e3.symm.trans e1.symm))))

omit [CompactSpace (AdeleQuotient F)] in
theorem envelopingAction_generator_mul (X : RealLieAlgebra F n) (a : EnvelopingAlgebra F n)
    (h : S.Space) :
    S.envelopingAction (envelopingGenerator F n (complexify F n X) * a) h =
      S.lieOperator X (S.envelopingAction a h) :=
  LinearMap.congr_fun (map_mul S.envelopingAction _ a) h

variable (F n) in
omit [CompactSpace (AdeleQuotient F)] in
theorem smoothEnvelopingAction_generator_apply (X : RealLieAlgebra F n)
    (f : SmoothFunctions F n) :
    envelopingAction F n (envelopingGenerator F n (complexify F n X)) f =
      smoothDifferential F n X f :=
  LinearMap.congr_fun (envelopingAction_real_generator F n X) f

/-- Genuine differential covariance for the whole enveloping algebra. -/
theorem coefficientMap_envelopingAction (hS : S.IsCuspidal) (a : EnvelopingAlgebra F n) :
    ∀ h : S.Space, coefficientMap S w hS (S.envelopingAction a h) =
      envelopingAction F n a (coefficientMap S w hS h) := by
  induction a using enveloping_real_left_induction with
  | h1 =>
    intro h
    simp only [map_one, Module.End.one_apply]
  | hadd a b ha hb =>
    intro h
    simp only [map_add, LinearMap.add_apply, ha, hb]
  | hsmul z a ha =>
    intro h
    simp only [map_smul, LinearMap.smul_apply, ha]
  | hgen X a ha =>
    intro h
    exact (congrArg (coefficientMap S w hS) (envelopingAction_generator_mul S X a h)).trans
      ((coefficientMap_lieOperator S w hS X _).trans
        ((congrArg (smoothDifferential F n X) (ha h)).trans
          ((smoothEnvelopingAction_generator_apply F n X _).symm.trans
            (envelopingAction_mul F n _ a _).symm)))

end Covariance

end Langlands.Automorphic.CuspidalHilbertOrbitCoefficientProof

namespace Langlands.Automorphic

open CuspidalHilbertOrbitCoefficientProof

/-- Smoothness, genuine differential covariance and joint finiteness of the actual
determinant-band Hilbert orbit coefficients. -/
theorem cuspidalHilbertOrbitCoefficient : CuspidalHilbertOrbitCoefficientStatement.{u} :=
  cuspidalHilbertOrbitCoefficientStatement_of_covariant fun _ _ _ _ _ T _ w =>
    ⟨fun f g => integrable_orbitIntegrand T.realization w T.cuspidal f g,
      coefficientMap T.realization w T.cuspidal, fun _ _ => rfl,
      fun a f => coefficientMap_envelopingAction T.realization w T.cuspidal a f⟩

end Langlands.Automorphic
