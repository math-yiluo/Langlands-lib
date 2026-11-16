import Langlands.Representation.Archimedean.RealMixedSwapTwistPrincipal
import Langlands.Representation.Archimedean.RealMixedSwapParameters
import Langlands.Representation.Archimedean.RealBlockRotation
import Langlands.Representation.Archimedean.PrincipalSeriesExtension

/-!
# Determinant-sign correction for signed real reversal
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean.RealMixedSwapTwist

open Langlands.GeneralLinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The determinant-sign character on the actual real general linear group. -/
def signDet (g : G) : ℂ := ((((g : A).det / |(g : A).det|) : ℝ) : ℂ)

theorem signDet_eq_unitSign (g : G) :
    signDet g = unitSign (Matrix.GeneralLinearGroup.det g) := rfl

theorem signDet_mul (g h : G) : signDet (g * h) = signDet g * signDet h := by
  simp only [signDet, Units.val_mul, Matrix.det_mul, abs_mul, mul_div_mul_comm,
    Complex.ofReal_mul]

@[simp] theorem signDet_one : signDet (1 : G) = 1 := by
  simp [signDet]

theorem signDet_sq (g : G) : signDet g ^ 2 = 1 :=
  unitSign_sq (Matrix.GeneralLinearGroup.det g)

theorem signDet_inv (g : G) : signDet g⁻¹ = signDet g := by
  simp only [signDet_eq_unitSign, map_inv, unitSign_inv]

theorem signDet_theta (g : G) : signDet (theta g) = signDet g := by
  have h : Matrix.GeneralLinearGroup.det (theta g) = Matrix.GeneralLinearGroup.det g⁻¹ := by
    apply Units.ext
    exact Matrix.det_transpose _
  rw [signDet_eq_unitSign, h, ← signDet_eq_unitSign, signDet_inv]

@[simp] theorem signDet_w : signDet w = 1 := by
  simp only [signDet, w_val, det_wMat, abs_one, div_self one_ne_zero, Complex.ofReal_one]

theorem signDet_twist (g : G) : signDet (twist g) = signDet g := by
  rw [twist, signDet_mul, signDet_w, one_mul, signDet_theta]

theorem signDet_diagonal (a : Fin 3 → ℝˣ) :
    signDet (Iwasawa.diagonalUnits a : G) = ∏ i : Fin 3, unitSign (a i) := by
  simp only [signDet, Iwasawa.diagonalUnits_val, Matrix.det_diagonal,
    Finset.abs_prod, unitSign]
  rw [← Finset.prod_div_distrib]
  push_cast
  rfl

theorem signDet_upperUnipotent (u : upperUnipotent 3 ℝ) : signDet (u : G) = 1 := by
  have hdet : (((u : G) : A).det) = 1 := by
    rw [Matrix.det_of_isUpperTriangular u.2.1]
    exact Finset.prod_eq_one fun i _ => u.2.2 i
  simp only [signDet, hdet, abs_one, div_self one_ne_zero, Complex.ofReal_one]

theorem signDet_blockRotation (p : ℕ) (t : ℝ) : signDet (blockRotation 3 p t) = 1 := by
  rw [show t = t / 2 + t / 2 by ring, RealBlockRotation.blockRotation_add,
    signDet_mul, ← sq, signDet_sq]

theorem contMDiff_signDet :
    ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ signDet := by
  refine contMDiff_of_contDiffOn (ψ := fun Y : A => ((Y.det / |Y.det| : ℝ) : ℂ))
    ?_ fun _ => rfl
  intro Y hY
  have hdet : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY).ne_zero
  have hd : ContDiff ℝ ∞ (fun Y : A => Y.det) :=
    PrincipalSeriesExtension.contDiff_det_comp fun p q =>
      PrincipalSeriesExtension.contDiff_entry p q
  have habs : ContDiffAt ℝ ∞ (fun Y : A => |Y.det|) Y :=
    (contDiffAt_abs hdet).comp Y hd.contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp Y
    (hd.contDiffAt.div habs (abs_ne_zero.mpr hdet))).contDiffWithinAt

theorem contMDiff_complex_mul {f h : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ f)
    (hh : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ h) :
    ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ (fun g => f g * h g) :=
  contMDiff_of_contDiffOn ((contDiffOn_unitsExtension hf).mul
    (contDiffOn_unitsExtension hh)) fun g => by rw [unitsExtension_val, unitsExtension_val]

theorem contMDiff_signDet_pow (q : ℕ) :
    ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ (fun g => signDet g ^ q) :=
  contMDiff_of_contDiffOn ((contDiffOn_unitsExtension contMDiff_signDet).pow q)
    fun g => by rw [unitsExtension_val]

/-- Signed pullback, with the determinant-sign power required by the mixed blocks. -/
def signedTwistLin (q : ℕ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := signDet g ^ q * f (twist g)
  map_add' f h := by funext g; simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem signedTwistLin_apply (q : ℕ) (f : G → ℂ) (g : G) :
    signedTwistLin q f g = signDet g ^ q * f (twist g) := rfl

theorem signedTwistLin_signedTwistLin (q : ℕ) (f : G → ℂ) :
    signedTwistLin q (signedTwistLin q f) = f := by
  funext g
  simp only [signedTwistLin_apply, signDet_twist, twist_twist]
  rw [← mul_assoc, ← mul_pow, ← sq, signDet_sq, one_pow, one_mul]

theorem contMDiff_signedTwistLin (q : ℕ) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ (signedTwistLin q f) :=
  contMDiff_complex_mul (contMDiff_signDet_pow q) (contMDiff_twistLin hf)

theorem rightTranslation_signedTwistLin (q : ℕ) (f : G → ℂ)
    (k : unitaryCompact ℝ 3) :
    Whittaker.rightTranslation ℂ G (k : G) (signedTwistLin q f) =
      signDet (k : G) ^ q •
        signedTwistLin q (Whittaker.rightTranslation ℂ G (k : G) f) := by
  funext g
  change signDet (g * k) ^ q * f (twist (g * k)) =
    signDet (k : G) ^ q * (signDet g ^ q * f (twist g * k))
  rw [signDet_mul, mul_pow, twist_mul_compact g k.2]
  ring

theorem signedTwistLin_mem_kFiniteVectors (q : ℕ) {f : G → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ 3)) :
    signedTwistLin q f ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ 3) := by
  refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
  have hfin := (mem_kFiniteVectors_iff _ _ _).mp hf
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range
    fun k : unitaryCompact ℝ 3 => Whittaker.rightTranslation ℂ G (k : G) f)).map
      (signedTwistLin q)) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  change Whittaker.rightTranslation ℂ G (k : G) (signedTwistLin q f) ∈ _
  rw [rightTranslation_signedTwistLin]
  exact Submodule.smul_mem _ _
    ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩

theorem blockFourierCoefficient_signedTwistLin (q : ℕ) (p : Fin 2) (k : ℤ)
    (f : G → ℂ) (g : G) :
    blockFourierCoefficient 3 p k (signedTwistLin q f) g =
      signDet g ^ q * blockFourierCoefficient 3 (1 - p.val) k f (twist g) := by
  unfold blockFourierCoefficient
  simp only [signedTwistLin_apply, signDet_mul, signDet_blockRotation, one_mul,
    twist_blockRotation_mul, mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

theorem principalSeriesCharacter_sign (q : ℕ) {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin 3) (x : ℝˣ), χ' j x = unitSign x ^ q * χ j x)
    (a : Fin 3 → ℝˣ) :
    principalSeriesCharacter ℝ 3 χ' a =
      signDet (Iwasawa.diagonalUnits a : G) ^ q * principalSeriesCharacter ℝ 3 χ a := by
  rw [signDet_diagonal, ← Finset.prod_pow]
  unfold principalSeriesCharacter
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [hχ' j]; ring

theorem signedTwistLin_mem_principalSeries (q : ℕ) {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin 3) (x : ℝˣ), χ' j x = unitSign x ^ q * χ (Fin.rev j) x⁻¹)
    {f : G → ℂ} (hf : f ∈ principalSeries ℝ 3 χ) :
    signedTwistLin q f ∈ principalSeries ℝ 3 χ' := by
  have hrev (j : Fin 3) : 2 - (j : ℕ) = (Fin.rev j : ℕ) := by
    rw [Fin.val_rev]
    omega
  have hu : twistLin f ∈ principalSeries ℝ 3 (reverseCharacters χ) :=
    twistLin_mem_principalSeries (fun j x => by
      simp only [reverseCharacters, hrev]) hf
  have hs (j : Fin 3) (x : ℝˣ) :
      χ' j x = unitSign x ^ q * reverseCharacters χ j x := by
    simpa only [reverseCharacters, hrev] using hχ' j x
  have hc := principalSeriesCharacter_sign q hs
  refine ⟨contMDiff_signedTwistLin q hf.1, fun a u g => ?_⟩
  change signDet (_ * _ * g) ^ q * twistLin f (_ * _ * g) =
    principalSeriesCharacter ℝ 3 χ' a * (signDet g ^ q * twistLin f g)
  rw [hu.2, signDet_mul, signDet_mul, signDet_upperUnipotent, mul_one, mul_pow,
    hc]
  ring

theorem signedTwistLin_mem_kFiniteFunctions (q : ℕ) {χ χ' : ℕ → ℝˣ → ℂ}
    (hχ' : ∀ (j : Fin 3) (x : ℝˣ), χ' j x = unitSign x ^ q * χ (Fin.rev j) x⁻¹)
    {f : G → ℂ} (hf : f ∈ kFiniteFunctions (principalSeries ℝ 3 χ) (unitaryCompact ℝ 3)) :
    signedTwistLin q f ∈ kFiniteFunctions (principalSeries ℝ 3 χ') (unitaryCompact ℝ 3) :=
  ⟨signedTwistLin_mem_principalSeries q hχ' hf.1, signedTwistLin_mem_kFiniteVectors q hf.2⟩

end Langlands.Archimedean.RealMixedSwapTwist
