import Langlands.Global.RankinSelberg.SchwartzBruhatProof.ArchFourier
import Langlands.Global.RankinSelberg.SchwartzBruhatProof.FiniteFourier
import Langlands.Global.RankinSelberg.EqualAnalyticPoisson
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Fourier inversion on `S(𝔸^n)`

Write a standard additive character as `ψ = ψ₀(b ·)` with `b ∈ F^×`. The Fourier transform of
a pure tensor `Φ_∞ ⊗ Φ_f` factors as `c_n F_∞ Φ_∞ ⊗ F_f Φ_f`, where `F_∞` is the Fourier
transform for the trace pairing `(v, w) ↦ Tr_∞(b Σ_j v_j w_j)` and `F_f` the finite-adelic
transform for `ψ_f`. Both factors satisfy inversion up to a constant, so for `Φ_f` invariant
under `L_m^n` the double transform is `K_m Φ(-x)`. Poisson summation applied to
`G ⊗ 1_(L_m^n)` and to its transform, for a nonnegative bump function `G` with `G(0) = 1`,
forces `K_m = 1`. Linearity then gives `Φ̂ ∈ S(𝔸^n)` and `Φ̂̂(x) = Φ(-x)` on all of
`S(𝔸^n)`.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped Classical FourierTransform
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker
open Langlands.Global.RankinSelbergGlobal.EqualAnalytic

attribute [local instance] finiteFourierMeasurableSpace finiteFourierBorelSpace
  finiteFourierSecondCountable finiteFourierLocallyCompact

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

/-! ### Coordinates of negated row vectors -/

theorem archimedeanCoordinates_zero : archimedeanCoordinates F n 0 = 0 := by
  have h := archimedeanCoordinates_add F n 0 0
  rw [add_zero] at h
  simpa using h

theorem archimedeanCoordinates_neg (x : RowVector F n) :
    archimedeanCoordinates F n (-x) = -archimedeanCoordinates F n x := by
  have h := archimedeanCoordinates_add F n x (-x)
  rw [add_neg_cancel, archimedeanCoordinates_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem finiteCoordinates_zero : finiteCoordinates F n 0 = 0 := by
  have h := finiteCoordinates_add F n 0 0
  rw [add_zero] at h
  simpa using h

theorem finiteCoordinates_neg (x : RowVector F n) :
    finiteCoordinates F n (-x) = -finiteCoordinates F n x := by
  have h := finiteCoordinates_add F n x (-x)
  rw [add_neg_cancel, finiteCoordinates_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-! ### The archimedean trace pairing -/

theorem traceBilin_symm (b : F) (w ξ : ArchRow F n) :
    traceBilin F n (mixedEmbedding F b) w ξ = traceBilin F n (mixedEmbedding F b) ξ w := by
  change mixedTrace F (_ * ∑ j, w j * ξ j) = mixedTrace F (_ * ∑ j, ξ j * w j)
  simp_rw [mul_comm (w _) (ξ _)]

theorem traceBilin_nondegenerate (b : F) (hb : b ≠ 0) (ξ : ArchRow F n)
    (h : ∀ w, traceBilin F n (mixedEmbedding F b) w ξ = 0) : ξ = 0 :=
  tracePairing_separates F n (mixedEmbedding F b) (mixedEmbedding F b⁻¹)
    (by rw [← map_mul, mul_inv_cancel₀ hb, map_one]) ξ fun _ => h _

theorem pairingFourier_const_mul (B : ArchRow F n →ₗ[ℝ] ArchRow F n →ₗ[ℝ] ℝ) (c : ℂ)
    (φ : ArchRow F n → ℂ) (ξ : ArchRow F n) :
    pairingFourier volume B (fun w => c * φ w) ξ = c * pairingFourier volume B φ ξ := by
  unfold pairingFourier
  simp_rw [mul_assoc]
  exact integral_const_mul c _

/-! ### Pure tensors -/

variable [CompactSpace (AdeleQuotient F)]

/-- The Fourier transform of a pure tensor is `c_n F_∞ Φ_∞ ⊗ F_f Φ_f`. -/
theorem fourierTransform_pure_eq (ψ : AddChar (Adeles F) ℂ) (b : F)
    (hb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x))
    (Φinf : SchwartzMap (ArchRow F n) ℂ) (Φfin : FinRow F n → ℂ) (η : RowVector F n) :
    fourierTransform F n ψ (fun x => Φinf (archimedeanCoordinates F n x) *
        Φfin (finiteCoordinates F n x)) η =
      ((rowConstant F n : ℝ) : ℂ) *
        (pairingFourier volume (traceBilin F n (mixedEmbedding F b)) Φinf
            (archimedeanCoordinates F n η) *
          finFourier Measure.addHaar (rowPairing ψ n) Φfin (finiteCoordinates F n η)) := by
  rw [fourierTransform_pure F n ψ b hb, Complex.real_smul]
  rfl

/-- The constant `K_m = c_n² C_∞ ν(L_m^n) ν(L_(n_ψ - m)^n)` of the double transform of a pure
tensor whose finite factor is `L_m^n`-invariant. -/
def inversionConstant (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (C : ℂ) (m : FinitePlace F →₀ ℤ) : ℂ :=
  ((rowConstant F n : ℝ) : ℂ) ^ 2 * C *
    (((Measure.addHaar : Measure (FinRow F n)).real (latticeVec n m) : ℝ) : ℂ) *
    (((Measure.addHaar : Measure (FinRow F n)).real
      (latticeVec n (conductorDivisor ψ hψ - m)) : ℝ) : ℂ)

/-- For a pure tensor `Φ_∞ ⊗ Φ_f` with `Φ_f` invariant under `L_m^n`, the transform is again
a pure tensor and the double transform is `K_m Φ(-x)`. -/
theorem pure_inversion (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (b : F) (hb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x)) (C : ℂ)
    (hC : ∀ φ : SchwartzMap (ArchRow F n) ℂ,
      (∃ φ' : SchwartzMap (ArchRow F n) ℂ,
        ⇑φ' = pairingFourier volume (traceBilin F n (mixedEmbedding F b)) φ) ∧
      ∀ x, pairingFourier volume (traceBilin F n (mixedEmbedding F b))
        (pairingFourier volume (traceBilin F n (mixedEmbedding F b)) φ) x = C * φ (-x))
    (m : FinitePlace F →₀ ℤ) (Φinf : SchwartzMap (ArchRow F n) ℂ) {Φfin : FinRow F n → ℂ}
    (hcs : HasCompactSupport Φfin) (hinv : ∀ x, ∀ h ∈ latticeVec n m, Φfin (x + h) = Φfin x)
    {Φ : RowVector F n → ℂ}
    (hΦ : Φ = fun x => Φinf (archimedeanCoordinates F n x) * Φfin (finiteCoordinates F n x)) :
    IsPureSchwartzBruhat F n (fourierTransform F n ψ Φ) ∧
      ∀ x, fourierTransform F n ψ (fourierTransform F n ψ Φ) x =
        inversionConstant n ψ hψ C m * Φ (-x) := by
  subst hΦ
  obtain ⟨φ', hφ'⟩ := (hC Φinf).1
  obtain ⟨⟨hlc', hcs'⟩, hFF⟩ := finiteFourier_inversion ψ hψ n m hcs hinv
  set r : ℂ := ((rowConstant F n : ℝ) : ℂ) with hr
  have hFT : fourierTransform F n ψ (fun x => Φinf (archimedeanCoordinates F n x) *
      Φfin (finiteCoordinates F n x)) = fun x => (r • φ') (archimedeanCoordinates F n x) *
        finFourier Measure.addHaar (rowPairing ψ n) Φfin (finiteCoordinates F n x) := by
    funext η
    rw [fourierTransform_pure_eq n ψ b hb, smul_apply, hφ', smul_eq_mul, mul_assoc]
  refine ⟨⟨r • φ', _, hlc', hcs', hFT⟩, fun x => ?_⟩
  rw [hFT, fourierTransform_pure_eq n ψ b hb]
  have hcoe : ⇑(r • φ') = fun w =>
      r * pairingFourier volume (traceBilin F n (mixedEmbedding F b)) Φinf w := by
    funext w
    rw [smul_apply, hφ', smul_eq_mul]
  rw [hcoe, pairingFourier_const_mul, (hC Φinf).2, hFF]
  beta_reduce
  rw [archimedeanCoordinates_neg, finiteCoordinates_neg]
  unfold inversionConstant
  ring

/-! ### The inversion constant is one -/

/-- **Poisson summation pins the constant.** Applying Poisson summation to `G ⊗ 1_(L_m^n)`
and to its transform gives `K_m S = S` with `S = Σ_(ξ ∈ F^n) G(ξ) 1_(L_m^n)(ξ) ≥ 1`. -/
theorem inversionConstant_eq_one (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (b : F)
    (hb : ∀ x, ψ x = standardCharacter F (algebraMap F (Adeles F) b * x)) (C : ℂ)
    (hC : ∀ φ : SchwartzMap (ArchRow F n) ℂ,
      (∃ φ' : SchwartzMap (ArchRow F n) ℂ,
        ⇑φ' = pairingFourier volume (traceBilin F n (mixedEmbedding F b)) φ) ∧
      ∀ x, pairingFourier volume (traceBilin F n (mixedEmbedding F b))
        (pairingFourier volume (traceBilin F n (mixedEmbedding F b)) φ) x = C * φ (-x))
    (m : FinitePlace F →₀ ℤ) : inversionConstant n ψ hψ C m = 1 := by
  obtain ⟨G, -, hGc, hGs, hGr, hG0⟩ := exists_contDiff_tsupport_subset (E := ArchRow F n)
    (s := Set.univ) (x := 0) (n := ⊤) Filter.univ_mem
  have hGc' : HasCompactSupport (Complex.ofRealCLM ∘ G) := hGc.comp_left rfl
  obtain ⟨Gs, hGs'⟩ : ∃ Gs : SchwartzMap (ArchRow F n) ℂ, ∀ w, Gs w = (G w : ℂ) :=
    ⟨hGc'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hGs), fun w => rfl⟩
  have hGnn : ∀ w, 0 ≤ G w := fun w => (hGr ⟨w, rfl⟩).1
  have hLo := isOpen_latticeVec (F := F) n m
  have hLc := isCompact_latticeVec (F := F) n m
  have hcs0 := hasCompactSupport_cosetIndicator (latticeVec n m) hLo hLc 0
  have hinv0 : ∀ x, ∀ h ∈ latticeVec n m,
      cosetIndicator (latticeVec n m) 0 (x + h) = cosetIndicator (latticeVec n m) 0 x :=
    fun x _ hh => cosetIndicator_add _ 0 x hh
  obtain ⟨Φ0, hΦ0⟩ : ∃ Φ0 : RowVector F n → ℂ, Φ0 = fun x =>
      Gs (archimedeanCoordinates F n x) *
        cosetIndicator (latticeVec n m) 0 (finiteCoordinates F n x) := ⟨_, rfl⟩
  have hmem : Φ0 ∈ schwartzBruhat F n :=
    Submodule.subset_span ⟨Gs, _, isLocallyConstant_cosetIndicator _ hLo 0, hcs0, hΦ0⟩
  obtain ⟨hpure, hFF⟩ := pure_inversion n ψ hψ b hb C hC m Gs hcs0 hinv0 hΦ0
  have hmem' : fourierTransform F n ψ Φ0 ∈ schwartzBruhat F n := Submodule.subset_span hpure
  have P1 := hasSum_poisson F n ψ hψ hmem
  have P2 := hasSum_poisson F n ψ hψ hmem'
  rw [P1.tsum_eq] at P2
  set S := ∑' c : RatRow F n, Φ0 (ratRow F n c) with hS
  have hsum : Summable fun c : RatRow F n => Φ0 (ratRow F n c) := by
    have := summable_periodization F n (schwartzBruhat_properties F n hmem).2.2 0
    simpa using this
  have P3 : HasSum (fun η : RatRow F n => Φ0 (ratRow F n (-η))) S :=
    (Equiv.neg (RatRow F n)).hasSum_iff (f := fun c => Φ0 (ratRow F n c)) |>.mpr hsum.hasSum
  have P4 : HasSum (fun η : RatRow F n => inversionConstant n ψ hψ C m * Φ0 (ratRow F n (-η)))
      S := by
    convert P2 using 1
    funext η
    rw [hFF, ratRow_neg]
  have hKS := (P3.mul_left (inversionConstant n ψ hψ C m)).unique P4
  have hnn : ∀ c : RatRow F n, 0 ≤ (Φ0 (ratRow F n c)).re := by
    intro c
    rw [hΦ0]
    change 0 ≤ (Gs (archimedeanCoordinates F n (ratRow F n c)) *
      cosetIndicator (latticeVec n m) 0 (finiteCoordinates F n (ratRow F n c))).re
    rw [hGs']
    unfold cosetIndicator
    split_ifs
    · simpa using hGnn _
    · simp
  have h1 : (Φ0 (ratRow F n 0)).re = 1 := by
    rw [hΦ0, ratRow_zero]
    change (Gs (archimedeanCoordinates F n 0) *
      cosetIndicator (latticeVec n m) 0 (finiteCoordinates F n 0)).re = 1
    rw [archimedeanCoordinates_zero, finiteCoordinates_zero, hGs', hG0]
    simp [cosetIndicator]
  have hS1 : 1 ≤ S.re := h1 ▸ le_hasSum (Complex.hasSum_re hsum.hasSum) 0 fun j _ => hnn j
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hS1
    linarith
  exact mul_right_cancel₀ hS0 (hKS.trans (one_mul S).symm)

/-! ### Fourier inversion on `S(𝔸^n)` -/

/-- **Fourier stability and inversion.** For a standard additive character `ψ`, the Fourier
transform maps `S(𝔸^n)` to itself and `Φ̂̂(x) = Φ(-x)`. -/
theorem fourierTransform_mem_and_inversion (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) :
    fourierTransform F n ψ Φ ∈ schwartzBruhat F n ∧
      ∀ x, fourierTransform F n ψ (fourierTransform F n ψ Φ) x = Φ (-x) := by
  obtain ⟨b, hb0, hb⟩ := exists_eq_standardCharacter_mul F ψ hψ
  obtain ⟨C, hC⟩ := exists_pairingFourier_inversion (volume : Measure (ArchRow F n))
    (traceBilin F n (mixedEmbedding F b)) (traceBilin_symm n b)
    (traceBilin_nondegenerate n b hb0)
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨Φinf, Φfin, hlc, hcs, hΦ⟩ := h
    obtain ⟨m, hm⟩ := exists_latticeVec_invariant n hlc hcs
    obtain ⟨hpure, hFF⟩ := pure_inversion n ψ hψ b hb C hC m Φinf hcs hm hΦ
    refine ⟨Submodule.subset_span hpure, fun x => ?_⟩
    rw [hFF, inversionConstant_eq_one n ψ hψ b hb C hC m, one_mul]
  | zero =>
    simp only [fourierTransform_zero]
    exact ⟨zero_mem _, fun x => rfl⟩
  | add Φ Ψ hΦm hΨm hΦ hΨ =>
    rw [fourierTransform_add F n ψ hψ (schwartzBruhat_properties F n hΦm).2.1
      (schwartzBruhat_properties F n hΨm).2.1]
    refine ⟨add_mem hΦ.1 hΨ.1, fun x => ?_⟩
    rw [fourierTransform_add F n ψ hψ (schwartzBruhat_properties F n hΦ.1).2.1
      (schwartzBruhat_properties F n hΨ.1).2.1]
    simp only [Pi.add_apply, hΦ.2 x, hΨ.2 x]
  | smul c Φ _ hΦ =>
    rw [fourierTransform_smul, fourierTransform_smul]
    refine ⟨Submodule.smul_mem _ c hΦ.1, fun x => ?_⟩
    simp only [Pi.smul_apply, hΦ.2 x]

end Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof
