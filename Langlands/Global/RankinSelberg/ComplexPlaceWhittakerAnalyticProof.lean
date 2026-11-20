import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerBridge
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerRegularity
import Langlands.Global.ArchimedeanCharacterGrowth

/-!
# The analytic premise at a complex place

Proof of `ComplexPlaceWhittakerAnalyticStatement`. Let `T` be an actual cuspidal realization,
`w` a complex place, `b` a finite adelic point and `x` a vector. Then the function
`g ↦ W_x(ι_w(g) b)` on `GL_(r+1)(ℂ)` is smooth and has polynomial growth for Jacquet's height.
The Lie action at `w` of a real direction `X` on `x` gives its right derivative along `X`. As a
consequence, `ComplexPlaceFunctionalEquationLocalReductionStatement` proves the complex-place
functional equation from the two local functional equations, the minus-one premise and the
contragredient premise. See the paired Markdown.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct Manifold ContDiff Topology
  Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

namespace ComplexPlaceAnalytic

open Langlands.Global Langlands.Automorphic ArchimedeanWhittakerRegularity

private local instance analyticSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
private local instance analyticSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Height

variable {n : ℕ}

theorem complexMatrixHeight_inv (g : Langlands.GeneralLinear n ℂ) :
    complexMatrixHeight g⁻¹ = complexMatrixHeight g := by
  simp only [complexMatrixHeight, inv_inv, add_comm]

open scoped Matrix.Norms.Frobenius in
theorem complexMatrixHeight_eq_frobenius (g : Langlands.GeneralLinear n ℂ) :
    complexMatrixHeight g = ‖g.val‖ ^ 2 + ‖(g⁻¹).val‖ ^ 2 := by
  have hsq (A : Matrix (Fin n) (Fin n) ℂ) :
      ‖A‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
    rw [Matrix.frobenius_norm_def]
    simp only [Real.rpow_two]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  simp only [complexMatrixHeight, Finset.sum_add_distrib, hsq]

open scoped Matrix.Norms.Frobenius in
theorem two_le_complexMatrixHeight (hn : 0 < n) (g : Langlands.GeneralLinear n ℂ) :
    2 ≤ complexMatrixHeight g := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hab : 1 ≤ ‖g.val‖ * ‖(g⁻¹).val‖ := calc
    1 ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ := one_le_norm_one _
    _ = ‖g.val * (g⁻¹).val‖ := congrArg norm g.mul_inv.symm
    _ ≤ _ := Matrix.frobenius_norm_mul _ _
  rw [complexMatrixHeight_eq_frobenius]
  nlinarith [sq_nonneg (‖g.val‖ - ‖(g⁻¹).val‖)]

theorem norm_entry_sq_le_complexMatrixHeight (g : Langlands.GeneralLinear n ℂ) (i j : Fin n) :
    ‖g.val i j‖ ^ 2 ≤ complexMatrixHeight g := by
  calc
    _ ≤ ‖g.val i j‖ ^ 2 + ‖(g⁻¹).val i j‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
    _ ≤ ∑ k : Fin n, (‖g.val i k‖ ^ 2 + ‖(g⁻¹).val i k‖ ^ 2) :=
      Finset.single_le_sum (f := fun k : Fin n =>
        (‖g.val i k‖ ^ 2 + ‖(g⁻¹).val i k‖ ^ 2))
        (fun k _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
        (Finset.mem_univ j)
    _ ≤ complexMatrixHeight g := by
      apply Finset.single_le_sum
        (f := fun k : Fin n => ∑ l : Fin n,
          (‖g.val k l‖ ^ 2 + ‖(g⁻¹).val k l‖ ^ 2))
        (fun k _ => Finset.sum_nonneg fun l _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
        (Finset.mem_univ i)

theorem norm_entry_le_complexMatrixHeight (hn : 0 < n)
    (g : Langlands.GeneralLinear n ℂ) (i j : Fin n) :
    ‖g.val i j‖ ≤ complexMatrixHeight g := by
  have hs := norm_entry_sq_le_complexMatrixHeight g i j
  have hH := two_le_complexMatrixHeight hn g
  nlinarith [sq_nonneg (‖g.val i j‖ - complexMatrixHeight g)]

theorem norm_det_le_complexMatrixHeight (hn : 0 < n) (g : Langlands.GeneralLinear n ℂ) :
    ‖g.val.det‖ ≤ (n.factorial : ℝ) * complexMatrixHeight g ^ n :=
  Langlands.Global.norm_det_le_factorial_mul_pow hn g.val _
    (norm_entry_le_complexMatrixHeight hn g)

/-- Every real power of `‖det g‖` is bounded by a constant times a power of Jacquet's height. -/
theorem exists_norm_det_rpow_le_complexMatrixHeight (hn : 0 < n) (β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear n ℂ,
      ‖g.val.det‖ ^ β ≤ C * complexMatrixHeight g ^ N := by
  let k : ℕ := ⌈|β|⌉₊
  refine ⟨(n.factorial : ℝ) ^ k, n * k, by positivity, fun g => ?_⟩
  let B := (n.factorial : ℝ) * complexMatrixHeight g ^ n
  have hH : 1 ≤ complexMatrixHeight g :=
    le_trans (by norm_num) (two_le_complexMatrixHeight hn g)
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le
    (Nat.one_le_cast.mpr (Nat.factorial_pos n)) (one_le_pow₀ hH)
  have hdet : 0 < ‖g.val.det‖ := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det g).ne_zero
  have hd : ‖g.val.det‖ ≤ B := norm_det_le_complexMatrixHeight hn g
  have hdi : ‖g.val.det‖⁻¹ ≤ B := by
    have hi := norm_det_le_complexMatrixHeight hn g⁻¹
    rw [complexMatrixHeight_inv] at hi
    have he : ((g⁻¹).val).det = (g.val.det)⁻¹ := by
      have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) g.mul_inv
      rw [Matrix.det_mul, Matrix.det_one] at h
      exact (inv_eq_of_mul_eq_one_right h).symm
    rwa [he, norm_inv] at hi
  have hl := Langlands.Global.abs_log_le_log_of_le hdet hd hdi
  calc
    ‖g.val.det‖ ^ β = Real.exp (Real.log ‖g.val.det‖ * β) :=
      Real.rpow_def_of_pos hdet β
    _ ≤ Real.exp (Real.log B * |β|) := by
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_right hl (abs_nonneg β)))
    _ = B ^ |β| := (Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hB) _).symm
    _ ≤ B ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hB (Nat.le_ceil _)
    _ = (n.factorial : ℝ) ^ k * complexMatrixHeight g ^ (n * k) := by
      rw [Real.rpow_natCast, mul_pow, pow_mul]

end Height

section Determinant

open Langlands.Global.ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

omit [NumberField F] in
theorem realProjection_det_complexPlaceGL (w : CP) (v : RP) (g : Langlands.GeneralLinear n ℂ) :
    realPlaceScalarProjection F v (complexPlaceGL F n w g).val.det = 1 := by
  rw [AlgHom.map_det]
  have he : (realPlaceScalarProjection F v).mapMatrix (complexPlaceGL F n w g).val =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j
    rfl
  rw [he, Matrix.det_one]

omit [NumberField F] in
theorem complexProjection_det_complexPlaceGL (w v : CP) (g : Langlands.GeneralLinear n ℂ) :
    complexPlaceScalarProjection F v (complexPlaceGL F n w g).val.det =
      ((Pi.mulSingle w g : CP → Langlands.GeneralLinear n ℂ) v).val.det := by
  rw [AlgHom.map_det]
  congr 1

/-- The adelic determinant norm of `ι_w(g)` is `‖det g‖²`. -/
theorem detNorm_complexPlacePoint (w : CP) (g : Langlands.GeneralLinear n ℂ) :
    detNorm F n (complexPlacePoint F n w g) = ‖g.val.det‖ ^ 2 := by
  let q : (InfiniteAdeles F)ˣ :=
    Matrix.GeneralLinearGroup.det ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w g))
  have hq : q.val = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (complexPlaceGL F n w g).val.det :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_det _).symm
  have hnorm (v : InfinitePlace F) :
      ‖q.val v‖ = if v = w.1 then ‖g.val.det‖ else 1 := by
    by_cases hv : v.IsReal
    · have hne : v ≠ w.1 := fun h => (InfinitePlace.not_isReal_iff_isComplex.mpr (h ▸ w.2)) hv
      rw [hq, infiniteAdeleCoordinates_symm_real F _ v hv]
      have he : ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
          ((complexPlaceGL F n w g).val.det.1 ⟨v, hv⟩)‖ =
          ‖(complexPlaceGL F n w g).val.det.1 ⟨v, hv⟩‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm) _
      rw [he]
      change ‖realPlaceScalarProjection F ⟨v, hv⟩ (complexPlaceGL F n w g).val.det‖ = _
      rw [realProjection_det_complexPlaceGL, norm_one, ite_eq_right hne]
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
      rw [hq, infiniteAdeleCoordinates_symm_complex F _ v hc]
      have he : ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm
          ((complexPlaceGL F n w g).val.det.2 ⟨v, hc⟩)‖ =
          ‖(complexPlaceGL F n w g).val.det.2 ⟨v, hc⟩‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm) _
      rw [he]
      change ‖complexPlaceScalarProjection F ⟨v, hc⟩ (complexPlaceGL F n w g).val.det‖ = _
      rw [complexProjection_det_complexPlaceGL]
      by_cases heq : v = w.1
      · have hsub : (⟨v, hc⟩ : CP) = w := Subtype.ext heq
        rw [hsub, Pi.mulSingle_eq_same, ite_eq_left heq]
      · have hsub : (⟨v, hc⟩ : CP) ≠ w := fun h => heq (congrArg Subtype.val h)
        rw [Pi.mulSingle_eq_of_ne hsub, Units.val_one, Matrix.det_one, norm_one, ite_eq_right heq]
  have hprod : ∏ v : InfinitePlace F, ‖q.val v‖ ^ v.mult = ‖g.val.det‖ ^ 2 := by
    rw [Finset.prod_eq_single w.1 (fun v _ hv => ?_) (by simp)]
    · rw [hnorm, ite_eq_left rfl, w.2.mult_eq_two]
    · rw [hnorm, ite_eq_right hv, one_pow]
  unfold detNorm
  rw [AdelicBlockDeterminantCharacter.determinantNorm_split]
  simp only [complexPlacePoint, adelicPoint, MulEquiv.apply_symm_apply,
    AdelicGL.infinite_pair, AdelicGL.finite_pair, map_one, mul_one]
  exact hprod

end Determinant

section Coordinates

open Langlands.Global.ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

/-- The archimedean matrix with `A` at the complex place `w` and the identity at every other
infinite place. -/
def complexPlaceMatrix (w : {v : InfinitePlace F // v.IsComplex})
    (A : Matrix (Fin n) (Fin n) ℂ) : ArchimedeanMatrix F n :=
  placeMatrixHom F n (1, Pi.mulSingle w A)

/-- The archimedean matrix with `B` at the complex place `w` and zero at every other infinite
place, as a real-linear map: the real Lie algebra inclusion at `w`. -/
def complexDirection (w : {v : InfinitePlace F // v.IsComplex}) :
    Matrix (Fin n) (Fin n) ℂ →L[ℝ] ArchimedeanMatrix F n :=
  LinearMap.toContinuousLinearMap
    ((realLieAlgebraToMatrix F n).toLinearMap ∘ₗ (complexPlaceLieInclusion F n w).toLinearMap)

omit [NumberField F] in
theorem complexDirection_apply (w : {v : InfinitePlace F // v.IsComplex})
    (B : Matrix (Fin n) (Fin n) ℂ) :
    complexDirection w B = placeMatrixHom F n (0, Pi.single w B) := by
  have h : complexDirection w B = placeMatrixHom F n (0,
      @Pi.single _ (fun _ => Matrix (Fin n) (Fin n) ℂ) _
        (fun a b => Classical.propDecidable (a = b)) w B) := rfl
  rw [h]
  congr
  exact Subsingleton.elim _ _

omit [NumberField F] in
theorem complexPlaceMatrix_eq_add (w : {v : InfinitePlace F // v.IsComplex})
    (A : Matrix (Fin n) (Fin n) ℂ) :
    complexPlaceMatrix w A = complexPlaceMatrix w 0 + complexDirection w A := by
  rw [complexDirection_apply]
  refine funext fun i => funext fun j => Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · show (1 : Matrix (Fin n) (Fin n) ℝ) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j + 0
    exact (add_zero _).symm
  · show (Pi.mulSingle w A : CP → Matrix (Fin n) (Fin n) ℂ) v i j =
      (Pi.mulSingle w (0 : Matrix (Fin n) (Fin n) ℂ) : CP → Matrix (Fin n) (Fin n) ℂ) v i j +
        (Pi.single w A : CP → Matrix (Fin n) (Fin n) ℂ) v i j
    by_cases h : v = w
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, Pi.single_eq_same, Matrix.zero_apply,
        zero_add]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h,
        Matrix.zero_apply, add_zero]

omit [NumberField F] in
theorem complexPlaceMatrix_mul_complexDirection (w : {v : InfinitePlace F // v.IsComplex})
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    complexPlaceMatrix w A * complexDirection w B = complexDirection w (A * B) := by
  rw [complexDirection_apply, complexDirection_apply, complexPlaceMatrix,
    ← map_mul (placeMatrixHom F n)]
  congr 1
  refine Prod.ext (mul_zero _) (funext fun v => ?_)
  show (Pi.mulSingle w A : CP → Matrix (Fin n) (Fin n) ℂ) v *
      (Pi.single w B : CP → Matrix (Fin n) (Fin n) ℂ) v =
    (Pi.single w (A * B) : CP → Matrix (Fin n) (Fin n) ℂ) v
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]

theorem hasFDerivAt_complexPlaceMatrix (w : {v : InfinitePlace F // v.IsComplex})
    (M : Matrix (Fin n) (Fin n) ℂ) :
    HasFDerivAt (complexPlaceMatrix w) (complexDirection w : _ →L[ℝ] ArchimedeanMatrix F n) M := by
  have h := (hasFDerivAt_const (complexPlaceMatrix w (0 : Matrix (Fin n) (Fin n) ℂ)) M).add
    (complexDirection w : _ →L[ℝ] ArchimedeanMatrix F n).hasFDerivAt
  rw [zero_add] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun A => complexPlaceMatrix_eq_add w A)

theorem contDiff_complexPlaceMatrix (w : {v : InfinitePlace F // v.IsComplex}) :
    ContDiff ℝ ∞ (complexPlaceMatrix w : Matrix (Fin n) (Fin n) ℂ → ArchimedeanMatrix F n) := by
  have h : (complexPlaceMatrix w : Matrix (Fin n) (Fin n) ℂ → ArchimedeanMatrix F n) =
      fun A => complexPlaceMatrix w 0 + complexDirection w A :=
    funext fun A => complexPlaceMatrix_eq_add w A
  rw [h]
  exact contDiff_const.add (complexDirection w).contDiff

omit [NumberField F] in
theorem complexPlaceGL_val (w : {v : InfinitePlace F // v.IsComplex})
    (g : Langlands.GeneralLinear n ℂ) :
    ((complexPlaceGL F n w g : ArchimedeanGL F n) : ArchimedeanMatrix F n) =
      complexPlaceMatrix w (g : Matrix (Fin n) (Fin n) ℂ) := by
  refine funext fun i => funext fun j => Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · exact complexPlaceGL_entry_fst F n w g i j v
  · refine (complexPlaceGL_entry F n w v g i j).trans ?_
    show _ = (Pi.mulSingle w (g : Matrix (Fin n) (Fin n) ℂ) : CP → Matrix (Fin n) (Fin n) ℂ) v i j
    by_cases h : v = w
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, Units.val_one]

omit [NumberField F] in
theorem isUnit_complexPlaceMatrix (w : {v : InfinitePlace F // v.IsComplex})
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit M) : IsUnit (complexPlaceMatrix w M : ArchimedeanMatrix F n) := by
  obtain ⟨g, rfl⟩ := hM
  rw [← complexPlaceGL_val]
  exact (complexPlaceGL F n w g).isUnit

end Coordinates

section Analytic

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

omit [CompactSpace (AdeleQuotient F)] in
theorem complexPlacePoint_mul_finitePoint (w : {v : InfinitePlace F // v.IsComplex}) {n : ℕ}
    (g : Langlands.GeneralLinear n ℂ) (b : FiniteAdelicGL F n) :
    complexPlacePoint F n w g * finitePoint F n b = adelicPoint F n (complexPlaceGL F n w g) b := by
  rw [complexPlacePoint, finitePoint, mul_adelicPoint, archPart_adelicPoint, finPart_adelicPoint,
    mul_one, one_mul]

/-- The Lie action at `w` of the real direction `X` is the enveloping derivative along the
archimedean matrix `X` at `w`. -/
theorem complexPlaceLieAction_eq_lieDeriv (w : {v : InfinitePlace F // v.IsComplex})
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : T.Space) :
    T.realization.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x =
      lieDeriv T (complexDirection w X) x := rfl

theorem cuspWhittaker_complexPlace (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (b : FiniteAdelicGL F (r + 1)) (v : T.Space) (g : Langlands.GeneralLinear (r + 1) ℂ) :
    cuspWhittaker F T χ v (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) =
      archWhittakerExt T χ v b (complexPlaceMatrix w (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)) :=
  (congrArg (cuspWhittaker F T χ v) (complexPlacePoint_mul_finitePoint w g b)).trans
    ((archWhittakerExt_units T χ hχ v b _).symm.trans
      (congrArg (archWhittakerExt T χ v b) (complexPlaceGL_val w g)))

theorem contDiffOn_archWhittakerExt_complexPlaceMatrix (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (b : FiniteAdelicGL F (r + 1)) (v : T.Space) :
    ContDiffOn ℝ ∞ (fun M => archWhittakerExt T χ v b (complexPlaceMatrix w M))
      {M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ | IsUnit M} :=
  (contDiffOn_archWhittakerExt T χ hχ v b).comp (contDiff_complexPlaceMatrix w).contDiffOn
    fun _ hM => isUnit_complexPlaceMatrix w hM

/-- The archimedean restriction `g ↦ W_v(ι_w(g) b)` is smooth. -/
theorem contMDiff_cuspWhittaker_complexPlace (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (b : FiniteAdelicGL F (r + 1)) (v : T.Space) :
    ContMDiff (Archimedean.matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g : Langlands.GeneralLinear (r + 1) ℂ =>
        cuspWhittaker F T χ v (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) :=
  Archimedean.contMDiff_of_contDiffOn
    (contDiffOn_archWhittakerExt_complexPlaceMatrix T χ hχ w b v)
    (cuspWhittaker_complexPlace T χ hχ w b v)

/-- The archimedean restriction `g ↦ W_x(ι_w(g) b)` has polynomial growth for Jacquet's
height. -/
theorem exists_norm_cuspWhittaker_complexPlace_le (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (b : FiniteAdelicGL F (r + 1)) (x : T.Space) :
    ∃ (C : ℝ) (N : ℕ), ∀ g : Langlands.GeneralLinear (r + 1) ℂ,
      ‖cuspWhittaker F T χ x (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)‖ ≤
        C * complexMatrixHeight g ^ N := by
  obtain ⟨β, hβ⟩ := exists_norm_cuspWhittaker_le T
  obtain ⟨C, hC0, hC⟩ := hβ χ hχ x
  obtain ⟨C', N, -, hC'⟩ :=
    exists_norm_det_rpow_le_complexMatrixHeight (Nat.succ_pos r) (2 * β)
  have hdb0 : 0 ≤ detNorm F (r + 1) (finitePoint F (r + 1) b) ^ β :=
    Real.rpow_nonneg (Unfolding.detNorm_pos F (r + 1) _).le _
  refine ⟨C * detNorm F (r + 1) (finitePoint F (r + 1) b) ^ β * C', N, fun g => ?_⟩
  have e : detNorm F (r + 1) (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) ^ β =
      ‖(g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ).det‖ ^ (2 * β) *
        detNorm F (r + 1) (finitePoint F (r + 1) b) ^ β := by
    rw [Unfolding.detNorm_mul, detNorm_complexPlacePoint,
      Real.mul_rpow (by positivity) (Unfolding.detNorm_pos F (r + 1) _).le,
      ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  calc _ ≤ C * detNorm F (r + 1)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) ^ β := hC _
    _ = C * (‖(g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ).det‖ ^ (2 * β) *
        detNorm F (r + 1) (finitePoint F (r + 1) b) ^ β) := by rw [e]
    _ ≤ C * (C' * complexMatrixHeight g ^ N *
        detNorm F (r + 1) (finitePoint F (r + 1) b) ^ β) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hC' g) hdb0) hC0
    _ = C * detNorm F (r + 1) (finitePoint F (r + 1) b) ^ β * C' *
        complexMatrixHeight g ^ N := by ring

/-- The Lie action at `w` of a real direction `X` on `x` gives the right derivative along `X`
of `g ↦ W_x(ι_w(g) b)`. -/
theorem cuspWhittaker_complexPlaceLieAction (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsComplex})
    (b : FiniteAdelicGL F (r + 1)) (x : T.Space) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    (fun g : Langlands.GeneralLinear (r + 1) ℂ => cuspWhittaker F T χ
        (T.realization.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
      Archimedean.rightDerivative (Archimedean.matrixModel ℂ (r + 1)) X
        (fun g : Langlands.GeneralLinear (r + 1) ℂ => cuspWhittaker F T χ x
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) := by
  refine funext fun g => ?_
  refine Eq.trans ?_
    (Archimedean.rightDerivative_eq_fderiv (contMDiff_cuspWhittaker_complexPlace T χ hχ w b x) X g).symm
  have hev : Archimedean.unitsExtension (fun g : Langlands.GeneralLinear (r + 1) ℂ =>
        cuspWhittaker F T χ x (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =ᶠ[𝓝
          (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)]
      fun M => archWhittakerExt T χ x b (complexPlaceMatrix w M) := by
    filter_upwards [Units.isOpen.mem_nhds g.isUnit] with M hM
    have hM' : IsUnit M := hM
    rw [← hM'.unit_spec, Archimedean.unitsExtension_val]
    exact cuspWhittaker_complexPlace T χ hχ w b x hM'.unit
  refine Eq.trans ?_ (congrArg
    (fun L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ →L[ℝ] ℂ =>
      L ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) * X))
    (hev.fderiv_eq (𝕜 := ℝ))).symm
  have hG := complexPlaceGL_val w g
  have hA : HasFDerivAt (archWhittakerExt T χ x b)
      (fderiv ℝ (archWhittakerExt T χ x b)
        (complexPlaceMatrix w (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)))
      (complexPlaceMatrix w (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)) :=
    hG ▸ (hasFDerivAt_archWhittakerExt T χ hχ x b
      (complexPlaceGL F (r + 1) w g)).differentiableAt.hasFDerivAt
  have hcomp := (hA.comp (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hasFDerivAt_complexPlaceMatrix w _)).fderiv
  calc cuspWhittaker F T χ (T.realization.complexPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) =
      cuspWhittaker F T χ (lieDeriv T (complexDirection w X) x)
        (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) :=
        congrArg (fun y => cuspWhittaker F T χ y
          (complexPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))
          (complexPlaceLieAction_eq_lieDeriv T w X x)
    _ = archWhittakerExt T χ (lieDeriv T (complexDirection w X) x) b
        (complexPlaceMatrix w (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)) :=
      cuspWhittaker_complexPlace T χ hχ w b _ g
    _ = archWhittakerExt T χ (lieDeriv T (complexDirection w X) x) b
        ((complexPlaceGL F (r + 1) w g : ArchimedeanGL F (r + 1)) :
          ArchimedeanMatrix F (r + 1)) := by rw [hG]
    _ = fderiv ℝ (archWhittakerExt T χ x b)
        ((complexPlaceGL F (r + 1) w g : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1))
        (((complexPlaceGL F (r + 1) w g : ArchimedeanGL F (r + 1)) :
          ArchimedeanMatrix F (r + 1)) * complexDirection w X) :=
      (fderiv_archWhittakerExt_mul T χ hχ x b _ _).symm
    _ = fderiv ℝ (archWhittakerExt T χ x b)
        (complexPlaceMatrix w (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ))
        (complexDirection w ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) * X)) := by
      rw [hG, complexPlaceMatrix_mul_complexDirection]
    _ = _ := congrArg (fun L => L ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) * X)) hcomp.symm

end Analytic

end ComplexPlaceAnalytic

open ComplexPlaceAnalytic in
/-- **The analytic premise at a complex place.** -/
theorem complexPlaceWhittakerAnalytic : ComplexPlaceWhittakerAnalyticStatement.{u} :=
  fun _ _ _ _ χ hχ _ T w b x =>
    ⟨contMDiff_cuspWhittaker_complexPlace T χ hχ w b x,
      exists_norm_cuspWhittaker_complexPlace_le T χ hχ w b x,
      fun X => cuspWhittaker_complexPlaceLieAction T χ hχ w b x X⟩

/-- The complex-place functional equation follows from the two local functional equations, the
minus-one premise and the contragredient premise. -/
def ComplexPlaceFunctionalEquationLocalReductionStatement : Prop :=
  ComplexLocalUnequalFunctionalEquationStatement →
    ComplexLocalEqualFunctionalEquationStatement →
    ComplexPlaceMinusOneStatement.{u} → ComplexPlaceContragredientParameterStatement.{u} →
    ComplexPlaceFunctionalEquationStatement.{u}

/-- The analytic premise of `complexPlaceFunctionalEquationAnalyticReduction` is
`complexPlaceWhittakerAnalytic`. -/
theorem complexPlaceFunctionalEquationLocalReduction :
    ComplexPlaceFunctionalEquationLocalReductionStatement.{u} :=
  fun hU hE hsign hdual =>
    complexPlaceFunctionalEquationAnalyticReduction hU hE complexPlaceWhittakerAnalytic hsign hdual

end Langlands.Global.RankinSelbergGlobal
