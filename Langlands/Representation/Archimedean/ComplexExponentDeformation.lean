import Langlands.Representation.Archimedean.ComplexBlockRestriction
import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Exponent deformation for complex standard modules -/

noncomputable section

open scoped BigOperators ContDiff Manifold Matrix Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexExponentDeformation

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexDuality

variable {n : ℕ}

/-- The logarithm of the ratio of two consecutive tail Gram determinants on invertible matrices. -/
def diagonalLog (p : Fin n) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((Real.log (gramMinor p y) - Real.log (gramMinor ((p : ℕ) + 1) y) : ℝ) : ℂ)

theorem diagonalLog_mul_unitary (p : Fin n) (g : Langlands.GeneralLinear n ℂ)
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    diagonalLog p (↑(g * k)) = diagonalLog p (↑g) := by
  simp only [diagonalLog, Units.val_mul, gramMinor, tailGram_mul_unitary _ _ hk]

theorem diagonalLog_unitary (p : Fin n) {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) : diagonalLog p (↑k) = 0 := by
  rw [← one_mul k, diagonalLog_mul_unitary p 1 hk]
  simp [diagonalLog, gramMinor, tailGram_one]

theorem diagonalLog_borel_mul (p : Fin n) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    diagonalLog p (↑((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * ↑u * g)) =
      (Real.log (Complex.normSq (a p : ℂ)) : ℂ) + diagonalLog p (↑g) := by
  let P (j : ℕ) := ∏ i : {i : Fin n // j ≤ (i : ℕ)}, Complex.normSq (a i : ℂ)
  have hP (j : ℕ) : P j ≠ 0 := by
    unfold P
    exact (Finset.prod_pos (s := (Finset.univ : Finset {i : Fin n // j ≤ (i : ℕ)}))
      fun i _ => Complex.normSq_pos.mpr (a i).ne_zero).ne'
  have hp : P p = Complex.normSq (a p : ℂ) * P ((p : ℕ) + 1) :=
    prod_tail_succ p fun i => Complex.normSq (a i : ℂ)
  let b : Langlands.GeneralLinear n ℂ := Iwasawa.diagonalUnits a * ↑u
  have hlog (j : ℕ) :
      Real.log (gramMinor j (↑(b * g) : Matrix (Fin n) (Fin n) ℂ)) =
        Real.log (P j) + Real.log (gramMinor j (↑g : Matrix (Fin n) (Fin n) ℂ)) := by
    dsimp only [b]
    rw [Units.val_mul, gramMinor_borel_mul]
    exact Real.log_mul (hP j) (gramMinor_pos j g).ne'
  have hratio : Real.log (P p) =
      Real.log (Complex.normSq (a p : ℂ)) + Real.log (P ((p : ℕ) + 1)) := by
    rw [hp]
    exact Real.log_mul (Complex.normSq_pos.mpr (a p).ne_zero).ne' (hP ((p : ℕ) + 1))
  change diagonalLog p (↑(b * g)) = _
  simp only [diagonalLog, hlog p, hlog ((p : ℕ) + 1), hratio, ← Complex.ofReal_add]
  congr 1
  abel

private theorem contDiffAt_diagonalLog (p : Fin n) (g : Langlands.GeneralLinear n ℂ) :
    ContDiffAt ℝ ∞ (diagonalLog p) (↑g : Matrix (Fin n) (Fin n) ℂ) := by
  have h (j : ℕ) : ContDiffAt ℝ ∞
      (fun y : Matrix (Fin n) (Fin n) ℂ => Real.log (gramMinor j y)) (↑g) := by
    have hG : ContDiff ℝ ∞ (gramMinor j : Matrix (Fin n) (Fin n) ℂ → ℝ) :=
      Complex.reCLM.contDiff.comp (contDiff_tailGram j)
    exact hG.contDiffAt.log (gramMinor_pos j g).ne'
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((h p).sub (h ((p : ℕ) + 1)))

/-- The scalar multiplier that adds `z` to the exponent of the character at position `p`. -/
def multiplier (p : Fin n) (z : ℂ) (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  Complex.exp (z * diagonalLog p (↑g))

private theorem contMDiff_diagonalLog (p : Fin n) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞
      (fun g : Langlands.GeneralLinear n ℂ => diagonalLog p (↑g)) := by
  apply contMDiff_of_contDiffOn (ψ := diagonalLog p) _ (fun _ => rfl)
  intro y hy
  obtain ⟨g, rfl⟩ := (show IsUnit y from hy)
  exact (contDiffAt_diagonalLog p g).contDiffWithinAt

private theorem contMDiff_multiplier (p : Fin n) (z : ℂ) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (multiplier p z) := by
  apply contMDiff_of_contDiffOn (ψ := fun y => Complex.exp (z * diagonalLog p y)) _ (fun _ => rfl)
  intro y hy
  obtain ⟨g, rfl⟩ := (show IsUnit y from hy)
  exact (contDiffAt_const.mul (contDiffAt_diagonalLog p g)).cexp.contDiffWithinAt

theorem multiplier_mul_unitary (p : Fin n) (z : ℂ) (g : Langlands.GeneralLinear n ℂ)
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    multiplier p z (g * k) = multiplier p z g := by
  rw [multiplier, diagonalLog_mul_unitary p g hk]
  rfl

theorem multiplier_unitary (p : Fin n) (z : ℂ) {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) : multiplier p z k = 1 := by
  simp [multiplier, diagonalLog_unitary p hk]

private theorem multiplier_neg_mul (p : Fin n) (z : ℂ) (g : Langlands.GeneralLinear n ℂ) :
    multiplier p (-z) g * multiplier p z g = 1 := by
  rw [multiplier, multiplier, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]

private theorem multiplier_borel_mul (p : Fin n) (z : ℂ) (a : Fin n → ℂˣ)
    (u : upperUnipotent n ℂ) (g : Langlands.GeneralLinear n ℂ) :
    multiplier p z ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * ↑u * g) =
      Complex.exp (z * (Real.log (Complex.normSq (a p : ℂ)) : ℂ)) * multiplier p z g := by
  simp only [multiplier, diagonalLog_borel_mul, mul_add, Complex.exp_add]

/-- Add `z` to the exponent of a complex character, preserving its angular weight. -/
def shiftCharacter (d : ComplexCharacterData) (z : ℂ) : ComplexCharacterData :=
  Langlands.Archimedean.ComplexBlock.twist z d

/-- Shift the exponent of one character in the list. -/
def shiftAt (ds : List ComplexCharacterData) (p : ℕ) (z : ℂ) : List ComplexCharacterData :=
  ds.modify p fun d => shiftCharacter d z

@[simp] theorem length_shiftAt (ds : List ComplexCharacterData) (p : ℕ) (z : ℂ) :
    (shiftAt ds p z).length = ds.length := by simp [shiftAt]

@[simp] theorem shiftAt_append_cons (pre post : List ComplexCharacterData) (d : ComplexCharacterData)
    (z : ℂ) : shiftAt (pre ++ d :: post) pre.length z = pre ++ shiftCharacter d z :: post := by
  induction pre with
  | nil => rfl
  | cons h pre ih =>
    change h :: shiftAt (pre ++ d :: post) pre.length z = h :: (pre ++ shiftCharacter d z :: post)
    rw [ih]

private theorem character_shift (d : ComplexCharacterData) (z : ℂ) (a : ℂˣ) :
    ((shiftCharacter d z).character a : ℂ) =
      Complex.exp (z * (Real.log (Complex.normSq (a : ℂ)) : ℂ)) * (d.character a : ℂ) := by
  change borelFactor d.weight (2 * (d.exponent + z)) (a : ℂ) = _
  rw [d.character_eq, ← borelFactor_eq_cpow d.weight (2 * d.exponent) a.ne_zero,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  simp only [borelFactor, Complex.ofReal_mul, Nat.cast_ofNat, Complex.ofReal_ofNat]
  rw [show (Real.log ‖(a : ℂ)‖ : ℂ) * (2 * (d.exponent + z)) =
    z * (2 * (Real.log ‖(a : ℂ)‖ : ℂ)) + (Real.log ‖(a : ℂ)‖ : ℂ) * (2 * d.exponent) by ring,
    Complex.exp_add]
  ring

private theorem positionCharacter_shift (ds : List ComplexCharacterData) (p i : ℕ)
    (hp : p < ds.length) (z : ℂ) (a : ℂˣ) :
    complexPositionCharacter (shiftAt ds p z) i a =
      (if i = p then Complex.exp (z * (Real.log (Complex.normSq (a : ℂ)) : ℂ)) else 1) *
        complexPositionCharacter ds i a := by
  induction ds generalizing p i with
  | nil => simp at hp
  | cons d ds ih =>
    cases p with
    | zero =>
      cases i with
      | zero => simpa [shiftAt, List.modify, complexPositionCharacter] using character_shift d z a
      | succ i => simp [shiftAt, List.modify, complexPositionCharacter]
    | succ p =>
      cases i with
      | zero => simp [shiftAt, List.modify, complexPositionCharacter]
      | succ i =>
        simpa [shiftAt, List.modify, complexPositionCharacter] using
          ih p i (Nat.lt_of_succ_lt_succ hp)

private theorem principalSeriesCharacter_shift (ds : List ComplexCharacterData)
    (hds : ds.length = n) (p : Fin n) (z : ℂ) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (shiftAt ds p z)) a =
      Complex.exp (z * (Real.log (Complex.normSq (a p : ℂ)) : ℂ)) *
        principalSeriesCharacter ℂ n (complexPositionCharacter ds) a := by
  unfold principalSeriesCharacter
  have hp : (p : ℕ) < ds.length := by rw [hds]; exact p.isLt
  simp only [positionCharacter_shift ds _ _ hp, mul_assoc]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [Fin.val_eq_val, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

/-- The `U(n)`-finite standard module, viewed as a space of functions. -/
abbrev KF (n : ℕ) (ds : List ComplexCharacterData) :=
  Langlands.Automorphic.complexStandardKFinite n ds

private def multiplyLinear (p : Fin n) (z : ℂ) :
    (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun f g := multiplier p z g * f g
  map_add' f h := by ext g; exact mul_add _ _ _
  map_smul' c f := by
    ext g
    change multiplier p z g * (c * f g) = c * (multiplier p z g * f g)
    ring

private theorem multiplyLinear_translate (p : Fin n) (z : ℂ)
    (f : Langlands.GeneralLinear n ℂ → ℂ) {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) :
    multiplyLinear p z (Whittaker.rightTranslation ℂ _ k f) =
      Whittaker.rightTranslation ℂ _ k (multiplyLinear p z f) := by
  ext g
  change multiplier p z g * f (g * k) = multiplier p z (g * k) * f (g * k)
  rw [multiplier_mul_unitary p z g hk]

private theorem multiplyLinear_mem {ds es : List ComplexCharacterData} (p : Fin n) (z : ℂ)
    (hχ : ∀ a : Fin n → ℂˣ,
      principalSeriesCharacter ℂ n (complexPositionCharacter es) a =
        Complex.exp (z * (Real.log (Complex.normSq (a p : ℂ)) : ℂ)) *
          principalSeriesCharacter ℂ n (complexPositionCharacter ds) a)
    (f : KF n ds) : multiplyLinear p z f ∈ KF n es := by
  refine ⟨⟨ComplexJacquetLimit.contMDiff_mul_fun (contMDiff_multiplier p z) f.2.1.1, ?_⟩, ?_⟩
  · intro a u g
    change multiplier p z ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) * ↑u * g) *
      (f : Langlands.GeneralLinear n ℂ → ℂ) _ = _ *
        (multiplier p z g * (f : Langlands.GeneralLinear n ℂ → ℂ) g)
    rw [multiplier_borel_mul, f.2.1.2 a u g, hχ]
    ring
  · let ρ := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
    let W := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      ρ (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ))
    let : FiniteDimensional ℂ W := (mem_kFiniteVectors_iff _ _ _).mp f.2.2
    apply (mem_kFiniteVectors_iff _ _ _).mpr
    refine Submodule.finiteDimensional_of_le (S₂ := W.map (multiplyLinear p z)) ?_
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨ρ (k : Langlands.GeneralLinear n ℂ) f, Submodule.subset_span ⟨k, rfl⟩,
      multiplyLinear_translate p z f k.2⟩

private theorem principalSeriesCharacter_shift_reverse {ds : List ComplexCharacterData}
    (hds : ds.length = n) (p : Fin n) (z : ℂ) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter ds) a =
      Complex.exp (-z * (Real.log (Complex.normSq (a p : ℂ)) : ℂ)) *
        principalSeriesCharacter ℂ n (complexPositionCharacter (shiftAt ds p z)) a := by
  rw [principalSeriesCharacter_shift ds hds, ← mul_assoc, ← Complex.exp_add,
    neg_mul, neg_add_cancel, Complex.exp_zero, one_mul]

/-- Multiplication by the scalar and its reciprocal identify the `U(n)`-finite spaces. -/
def shiftEquiv (ds : List ComplexCharacterData) (hds : ds.length = n) (p : Fin n) (z : ℂ) :
    KF n ds ≃ₗ[ℂ] KF n (shiftAt ds p z) :=
  LinearEquiv.ofLinearMap
    (LinearMap.codRestrict _ ((multiplyLinear p z).comp (KF n ds).subtype)
      (multiplyLinear_mem p z (principalSeriesCharacter_shift ds hds p z)))
    (LinearMap.codRestrict _ ((multiplyLinear p (-z)).comp (KF n (shiftAt ds p z)).subtype)
      (multiplyLinear_mem p (-z) (principalSeriesCharacter_shift_reverse hds p z)))
    (by
      ext f g
      change multiplier p z g * (multiplier p (-z) g * (f : Langlands.GeneralLinear n ℂ → ℂ) g) = _
      rw [← mul_assoc, mul_comm (multiplier p z g), multiplier_neg_mul, one_mul]
      rfl)
    (by
      ext f g
      change multiplier p (-z) g * (multiplier p z g * (f : Langlands.GeneralLinear n ℂ → ℂ) g) = _
      rw [← mul_assoc, multiplier_neg_mul, one_mul]
      rfl)

theorem shiftEquiv_apply (ds : List ComplexCharacterData) (hds : ds.length = n) (p : Fin n)
    (z : ℂ) (f : KF n ds) (g : Langlands.GeneralLinear n ℂ) :
    (shiftEquiv ds hds p z f : Langlands.GeneralLinear n ℂ → ℂ) g =
      multiplier p z g * (f : Langlands.GeneralLinear n ℂ → ℂ) g := rfl

private theorem shiftEquiv_symm_apply (ds : List ComplexCharacterData) (hds : ds.length = n)
    (p : Fin n) (z : ℂ) (f : KF n (shiftAt ds p z)) (g : Langlands.GeneralLinear n ℂ) :
    ((shiftEquiv ds hds p z).symm f : Langlands.GeneralLinear n ℂ → ℂ) g =
      multiplier p (-z) g * (f : Langlands.GeneralLinear n ℂ → ℂ) g := rfl

theorem shiftEquiv_rep {ds : List ComplexCharacterData} (hds : ds.length = n) (p : Fin n) (z : ℂ)
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n ds) :
    shiftEquiv ds hds p z (complexStandardRep n ds k f) =
      complexStandardRep n (shiftAt ds p z) k (shiftEquiv ds hds p z f) := by
  apply Subtype.ext
  rw [principalSeriesRep_apply_coe]
  exact multiplyLinear_translate p z f k.2

private theorem rightDerivative_multiplier (p : Fin n) (z : ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (multiplier p z) g =
      multiplier p z g * z *
        rightDerivative (matrixModel ℂ n) X
          (fun h : Langlands.GeneralLinear n ℂ => diagonalLog p ↑h) g := by
  have he {φ : Matrix (Fin n) (Fin n) ℂ → ℂ} :
      unitsExtension (fun h : Langlands.GeneralLinear n ℂ => φ ↑h) =ᶠ[nhds
        (↑g : Matrix (Fin n) (Fin n) ℂ)] φ := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit g)] with y hy
    obtain ⟨h, rfl⟩ := hy
    exact unitsExtension_val _ h
  have hd := (((contDiffAt_diagonalLog p g).differentiableAt (by simp)).hasFDerivAt.const_mul z).cexp
  rw [rightDerivative_eq_fderiv (contMDiff_multiplier p z),
    rightDerivative_eq_fderiv (contMDiff_diagonalLog p)]
  change fderiv ℝ (unitsExtension (fun h => Complex.exp (z * diagonalLog p ↑h))) (↑g)
      ((↑g : Matrix (Fin n) (Fin n) ℂ) * X) = _
  rw [(he (φ := fun y => Complex.exp (z * diagonalLog p y))).fderiv_eq,
    (he (φ := diagonalLog p)).fderiv_eq, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, multiplier, mul_assoc]

/-- The Lie operator at parameter `z`, transported back to the fixed space. -/
def transportedDerivative (ds : List ComplexCharacterData) (hds : ds.length = n)
    (p : Fin n) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (KF n ds) :=
  (shiftEquiv ds hds p z).symm.toLinearMap ∘ₗ
    complexStandardLie n (shiftAt ds p z) (1 ⊗ₜ X) ∘ₗ (shiftEquiv ds hds p z).toLinearMap

private theorem transportedDerivative_apply {ds : List ComplexCharacterData} (hds : ds.length = n)
    (p : Fin n) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (f : KF n ds)
    (g : Langlands.GeneralLinear n ℂ) :
    (transportedDerivative ds hds p z X f : Langlands.GeneralLinear n ℂ → ℂ) g =
      rightDerivative (matrixModel ℂ n) X f g +
        z * (rightDerivative (matrixModel ℂ n) X
          (fun h : Langlands.GeneralLinear n ℂ => diagonalLog p ↑h) g *
            (f : Langlands.GeneralLinear n ℂ → ℂ) g) := by
  simp only [transportedDerivative, LinearMap.comp_apply, LinearEquiv.coe_coe,
    shiftEquiv_symm_apply, principalSeriesLie_one_tmul_apply_coe]
  have hf : (shiftEquiv ds hds p z f : Langlands.GeneralLinear n ℂ → ℂ) =
      fun h => multiplier p z h * (f : Langlands.GeneralLinear n ℂ → ℂ) h :=
    funext (shiftEquiv_apply ds hds p z f)
  rw [hf, ComplexTemperedComplement.rightDerivative_mul_fun
    (contMDiff_multiplier p z) f.2.1.1, rightDerivative_multiplier, mul_add,
    ← mul_assoc (multiplier p (-z) g) _ (rightDerivative (matrixModel ℂ n) X f g),
    ← mul_assoc (multiplier p (-z) g) _ ((f : Langlands.GeneralLinear n ℂ → ℂ) g),
    ← mul_assoc (multiplier p (-z) g) _ (rightDerivative (matrixModel ℂ n) X _ g),
    ← mul_assoc (multiplier p (-z) g) _ z, multiplier_neg_mul]
  ring

/-- The transported operator is affine in the exponent shift. The constant coefficient is
the original Lie operator, and the linear coefficient is the difference at parameter `1`. -/
theorem transportedDerivative_affine {ds : List ComplexCharacterData} (hds : ds.length = n)
    (p : Fin n) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    transportedDerivative ds hds p z X =
      complexStandardLie n ds (1 ⊗ₜ X) +
        z • (transportedDerivative ds hds p 1 X - complexStandardLie n ds (1 ⊗ₜ X)) := by
  ext f g
  simp only [transportedDerivative_apply hds, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, principalSeriesLie_one_tmul_apply_coe]
  ring

end Langlands.Archimedean.ComplexExponentDeformation
