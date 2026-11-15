import Langlands.Global.RankinSelberg.EqualAnalyticModulus

/-! # Poisson summation twisted by `GL_n(𝔸)`

For `Φ ∈ S(𝔸^n)` and `g ∈ GL_n(𝔸)`,
`Σ_{ξ ∈ F^n} Φ(ξ g) = |det g|^(-1) Σ_{η ∈ F^n} Φ̂(η ᵗg^(-1))`, both series converging
absolutely. The translate `x ↦ Φ(x g)` is again continuous, integrable and dominated, and its
Fourier transform is `|det g|^(-1) Φ̂(· ᵗg^(-1))` by the change of variables `x ↦ x g`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped Classical Matrix
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

local instance poissonGLMeasurableSpace (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

local instance poissonGLBorelSpace (k m : ℕ) :
    BorelSpace (Matrix (Fin k) (Fin m) (Adeles F)) := ⟨rfl⟩

theorem archimedeanCoordinates_mul (n : ℕ) (x : RowVector F n)
    (M : Matrix (Fin n) (Fin n) (Adeles F)) (j : Fin n) :
    archimedeanCoordinates F n (x * M) j =
      ∑ i, archimedeanCoordinates F n x i * InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1 := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace F (∑ i, x 0 i * M i j).1 = _
  rw [adeles_sum_fst, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adeles_mul_fst, map_mul]
  rfl

theorem finiteCoordinates_mul (n : ℕ) (x : RowVector F n)
    (M : Matrix (Fin n) (Fin n) (Adeles F)) (j : Fin n) :
    finiteCoordinates F n (x * M) j = ∑ i, finiteCoordinates F n x i * (M i j).2 := by
  change (∑ i, x 0 i * M i j).2 = _
  rw [adeles_sum_snd]
  rfl

/-- The archimedean coordinates of `x M` are bounded by those of `x`. -/
theorem exists_norm_archimedeanCoordinates_mul_le (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (Adeles F)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : RowVector F n,
      ‖archimedeanCoordinates F n (x * M)‖ ≤ c * ‖archimedeanCoordinates F n x‖ := by
  refine ⟨∑ i, ∑ j, ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _, fun x => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [archimedeanCoordinates_mul]
  calc ‖∑ i, archimedeanCoordinates F n x i *
        InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖
      ≤ ∑ i, ‖archimedeanCoordinates F n x i‖ *
        ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_mul_le _ _)
    _ ≤ ∑ i, ‖archimedeanCoordinates F n x‖ *
        ∑ j, ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul (norm_le_pi_norm _ i)
          (Finset.single_le_sum (f := fun j => ‖InfiniteAdeleRing.ringEquiv_mixedSpace F
            (M i j).1‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j))
          (norm_nonneg _) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖InfiniteAdeleRing.ringEquiv_mixedSpace F (M i j).1‖) *
        ‖archimedeanCoordinates F n x‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-- Domination is preserved by right multiplication by an invertible matrix. -/
theorem IsRowDominated.comp_mul (n : ℕ) {Φ : RowVector F n → ℂ} (hΦ : IsRowDominated F n Φ)
    (g : AdelicGL F n) :
    IsRowDominated F n (fun x => Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))) := by
  obtain ⟨d, hd, hsupp, hdec⟩ := hΦ
  set M' := ((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))
  have hinv : ∀ x : RowVector F n,
      x * (g : Matrix (Fin n) (Fin n) (Adeles F)) * M' = x := by
    intro x
    simp only [M', Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  obtain ⟨e, he, hes⟩ := exists_integer_mul_mem_of_isCompact F
    (Set.finite_range fun p : Fin n × Fin n => (M' p.1 p.2).2).isCompact
  obtain ⟨c, hc0, hc⟩ := exists_norm_archimedeanCoordinates_mul_le F n M'
  refine ⟨d * e, mul_ne_zero hd he, fun x hx j => ?_, fun N => ?_⟩
  · have h1 := hsupp _ hx
    rw [← hinv x, finiteCoordinates_mul, Finset.mul_sum]
    refine sum_mem fun i _ => ?_
    have : algebraMap (𝓞 F) (FiniteAdeles F) (d * e) *
        (finiteCoordinates F n (x * (g : Matrix (Fin n) (Fin n) (Adeles F))) i * (M' i j).2) =
        (algebraMap (𝓞 F) (FiniteAdeles F) d *
          finiteCoordinates F n (x * (g : Matrix (Fin n) (Fin n) (Adeles F))) i) *
        (algebraMap (𝓞 F) (FiniteAdeles F) e * (M' i j).2) := by
      rw [map_mul]
      ring
    rw [this]
    exact mul_mem (h1 i) (hes _ ⟨(i, j), rfl⟩)
  · obtain ⟨K, hK⟩ := hdec N
    refine ⟨(1 + c) ^ N * K, fun x => ?_⟩
    have hK0 : 0 ≤ K := le_trans (by positivity) (hK x)
    have hx := hc (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))
    rw [hinv] at hx
    have h1 : 1 + ‖archimedeanCoordinates F n x‖ ≤ (1 + c) *
        (1 + ‖archimedeanCoordinates F n (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))‖) := by
      have := norm_nonneg (archimedeanCoordinates F n (x * (g : Matrix (Fin n) (Fin n) (Adeles F))))
      nlinarith
    calc (1 + ‖archimedeanCoordinates F n x‖) ^ N *
          ‖Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))‖
        ≤ ((1 + c) * (1 + ‖archimedeanCoordinates F n
            (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))‖)) ^ N *
          ‖Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 N) (norm_nonneg _)
      _ = (1 + c) ^ N * ((1 + ‖archimedeanCoordinates F n
            (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))‖) ^ N *
          ‖Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))‖) := by rw [mul_pow]; ring
      _ ≤ (1 + c) ^ N * K := mul_le_mul_of_nonneg_left (hK _) (by positivity)

/-- The pairing after a change of variables: `⟨x M, y⟩ = ⟨x, y ᵗM⟩`. -/
theorem rowPairing_mul (n : ℕ) (x y : RowVector F n) (M : Matrix (Fin n) (Fin n) (Adeles F)) :
    ∑ j, (x * M) 0 j * y 0 j = ∑ i, x 0 i * (y * Mᵀ) 0 i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem inverseTranspose_val (n : ℕ) (g : AdelicGL F n) :
    ((GeneralLinear.inverseTranspose n (Adeles F) g : AdelicGL F n) :
        Matrix (Fin n) (Fin n) (Adeles F)) =
      (((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F)))ᵀ := rfl

variable [CompactSpace (AdeleQuotient F)]

/-- The Fourier transform of `x ↦ Φ(x g)` is `|det g|^(-1) Φ̂(· ᵗg^(-1))`. -/
theorem fourierTransform_comp_mul (n : ℕ) (ψ : AddChar (Adeles F) ℂ) (Φ : RowVector F n → ℂ)
    (g : AdelicGL F n) (y : RowVector F n) :
    fourierTransform F n ψ (fun x => Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))) y =
      ((absDet F n g)⁻¹ : ℂ) * fourierTransform F n ψ Φ
        (y * ((GeneralLinear.inverseTranspose n (Adeles F) g : AdelicGL F n) :
          Matrix (Fin n) (Fin n) (Adeles F))) := by
  set M' := ((g⁻¹ : AdelicGL F n) : Matrix (Fin n) (Fin n) (Adeles F))
  have hinv : ∀ x : RowVector F n, x * (g : Matrix (Fin n) (Fin n) (Adeles F)) * M' = x := by
    intro x
    simp only [M', Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  unfold fourierTransform
  set f : RowVector F n → ℂ := fun z => Φ z * ψ (∑ j, (z * M') 0 j * y 0 j) with hf
  have hcomp : (fun x : RowVector F n => Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F))) *
      ψ (∑ j, x 0 j * y 0 j)) = fun x => f (x * (g : Matrix (Fin n) (Fin n) (Adeles F))) := by
    funext x
    simp only [hf, hinv]
  rw [hcomp, integral_comp_rightMul, inverseTranspose_val]
  rw [show ((absDet F n g)⁻¹ : ℝ) • ∫ x, f x ∂rectangleMeasure F 1 n =
    ((absDet F n g)⁻¹ : ℂ) * ∫ x, f x ∂rectangleMeasure F 1 n by
      rw [Complex.real_smul]; push_cast; rfl]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hf]
  rw [rowPairing_mul]

/-- **Poisson summation twisted by `g ∈ GL_n(𝔸)`.** -/
theorem hasSum_poisson_mul (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) (g : AdelicGL F n) :
    HasSum (fun η : RatRow F n => ((absDet F n g)⁻¹ : ℂ) * fourierTransform F n ψ Φ
        (ratRow F n η * ((GeneralLinear.inverseTranspose n (Adeles F) g : AdelicGL F n) :
          Matrix (Fin n) (Fin n) (Adeles F))))
      (∑' C : RatRow F n, Φ (ratRow F n C * (g : Matrix (Fin n) (Fin n) (Adeles F)))) := by
  obtain ⟨hc, hint, hdom⟩ := schwartzBruhat_properties F n hΦ
  have hhat := (fourierTransform_properties F n ψ hψ hΦ).2
  have h := hasSum_fourierTransform_ratRow F n ψ hψ
    (Φ := fun x => Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F))))
    (hc.comp (continuous_id.matrix_mul continuous_const))
    ((integrable_comp_rightMul_iff F n g Φ).mpr hint) (hdom.comp_mul F n g) (by
      have : fourierTransform F n ψ (fun x => Φ (x * (g : Matrix (Fin n) (Fin n) (Adeles F)))) =
          ((absDet F n g)⁻¹ : ℂ) • fun y => fourierTransform F n ψ Φ
            (y * ((GeneralLinear.inverseTranspose n (Adeles F) g : AdelicGL F n) :
              Matrix (Fin n) (Fin n) (Adeles F))) := by
        funext y
        rw [fourierTransform_comp_mul]
        rfl
      rw [this]
      exact (hhat.comp_mul F n _).smul _)
  simp only [fourierTransform_comp_mul] at h
  exact h

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic
