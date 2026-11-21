import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters

/-! # Polynomial height control for the actual block parabolic -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Opposite
open scoped CategoryTheory.MonObj BigOperators NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global

/-- Complex functions bounded by a polynomial in a specified height form
a subalgebra under pointwise operations. -/
def polynomialGrowthAlgebra {X : Type*} (H : X → ℝ) (hH : ∀ x, 1 ≤ H x) :
    Subalgebra ℂ (X → ℂ) where
  carrier := {f | ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ, ∀ x, ‖f x‖ ≤ C * H x ^ e}
  algebraMap_mem' c := ⟨max 1 ‖c‖, le_max_left _ _, 0, fun x => by simp⟩
  add_mem' := by
    rintro f g ⟨C, hC, e, hf⟩ ⟨D, hD, d, hg⟩
    refine ⟨C + D, by linarith, max e d, fun x => ?_⟩
    calc
      ‖(f + g) x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
      _ ≤ C * H x ^ e + D * H x ^ d := add_le_add (hf x) (hg x)
      _ ≤ C * H x ^ max e d + D * H x ^ max e d := add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hH x) (le_max_left _ _)) (zero_le_one.trans hC))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hH x) (le_max_right _ _)) (zero_le_one.trans hD))
      _ = _ := (add_mul _ _ _).symm
  mul_mem' := by
    rintro f g ⟨C, hC, e, hf⟩ ⟨D, hD, d, hg⟩
    refine ⟨C * D, one_le_mul_of_one_le_of_one_le hC hD, e + d, fun x => ?_⟩
    calc
      ‖(f * g) x‖ = ‖f x‖ * ‖g x‖ := norm_mul _ _
      _ ≤ (C * H x ^ e) * (D * H x ^ d) :=
        mul_le_mul (hf x) (hg x) (norm_nonneg _) (mul_nonneg (zero_le_one.trans hC)
          (pow_nonneg (zero_le_one.trans (hH x)) _))
      _ = _ := by rw [pow_add]; ring

namespace AdelicMatrixHeight

open Langlands.GeneralLinear MatrixInverseHeight AdelicBlockParabolic
open AdelicBlockDeterminantCharacter RepresentationGrowth

variable {n : ℕ} (B : BlockShape n)

private theorem localMaximum_leviProjection_le
    {R : Type v} [CommRing R] {K : Type w} [NormedField K] (f : R →+* K)
    (p : B.parabolic R) (i : Fin B.length) :
    localMaximum f (B.leviProjection R p i) ≤ localMaximum f p.val := by
  have h (q : B.parabolic R) :
      ‖fun a b : Fin (B.size i) => f (B.leviProjection R q i a b)‖ ≤ localMaximum f q.val := by
    have h₀ := localMaximum_nonneg f q.val
    apply (pi_norm_le_iff_of_nonneg h₀).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg h₀).mpr
    intro b
    rw [B.leviProjection_apply]
    exact entry_le_localMaximum f q.val (B.index i a) (B.index i b)
  have hi : (B.leviProjection R p i)⁻¹ = B.leviProjection R p⁻¹ i :=
    (congrFun (map_inv (B.leviProjection R) p) i).symm
  refine max_le (h p) ?_
  simp only [hi]
  simpa only [Subgroup.coe_inv, localMaximum_inv] using h p⁻¹

variable (F : Type u) [Field F] [NumberField F]

/-- The product of the dimension-scaled full adelic heights of the Levi blocks. -/
def blockProductHeight (m : FullLevi F B) : ℝ :=
  ∏ i, height F (B.size i) (m i)

theorem one_le_blockProductHeight (m : FullLevi F B) : 1 ≤ blockProductHeight B F m :=
  Finset.one_le_prod₀ fun i _ => one_le_height F _ (B.positive i) _

theorem blockHeight_le_blockProductHeight (m : FullLevi F B) (i : Fin B.length) :
    height F (B.size i) (m i) ≤ blockProductHeight B F m := by
  classical
  unfold blockProductHeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (zero_le_one.trans (one_le_height F _ (B.positive i) _))
    (Finset.one_le_prod₀ fun j _ => one_le_height F _ (B.positive j) _)

theorem height_leviProjection_le (p : Full F B) (i : Fin B.length) :
    height F (B.size i) (B.leviProjection (Adeles F) p i) ≤ height F n p.val := by
  have hs : B.size i ≤ n := calc
    B.size i ≤ ∑ j, B.size j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (B.size j)) (Finset.mem_univ i)
    _ = n := B.sum_eq
  have hn := (B.positive i).trans_le hs
  unfold height
  have hInf (v : InfinitePlace F) : infiniteLocal F (B.size i) (B.leviProjection (Adeles F) p i) v ≤
      infiniteLocal F n p.val v :=
    localMaximum_leviProjection_le B (infiniteProjection F v) p i
  have hFin (v : FinitePlace F) : finiteLocal F (B.size i) (B.leviProjection (Adeles F) p i) v ≤
      finiteLocal F n p.val v :=
    localMaximum_leviProjection_le B (finiteProjection F v) p i
  apply mul_le_mul
  · apply Finset.prod_le_prod₀
    · intro v _
      exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _
    · intro v _
      exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _))
        (mul_le_mul (by exact_mod_cast hs) (hInf v) (localMaximum_nonneg _ _) (Nat.cast_nonneg _)) _
  · exact finprod_le_finprod₀ (hasFiniteMulSupport_finiteLocal F _ (B.positive i) _)
      (fun _ => localMaximum_nonneg _ _) (hasFiniteMulSupport_finiteLocal F _ hn _) hFin
  · exact finprod_nonneg fun _ => localMaximum_nonneg _ _
  · exact Finset.prod_nonneg fun _ _ =>
      pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _

/-- The Levi height of a parabolic element is bounded by a power of its
full ambient height. -/
theorem blockProductHeight_leviProjection_le (p : Full F B) :
    blockProductHeight B F (B.leviProjection (Adeles F) p) ≤ height F n p.val ^ B.length := by
  calc
    _ ≤ ∏ _ : Fin B.length, height F n p.val :=
      Finset.prod_le_prod₀ (fun i _ => zero_le_one.trans (one_le_height F _ (B.positive i) _))
        (fun i _ => height_leviProjection_le B F p i)
    _ = _ := by simp

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints

local notation "𝕜" => CommRingCat.of F
local notation "GL[" b "]" => groupScheme (Fin b) 𝕜
local notation "std[" b "]" => MatrixRepresentation.standard (Fin b) 𝕜
local notation "det[" b "]" => determinantCharacter (Fin b) 𝕜

omit [NumberField F] in
private theorem characterUnits_det (R : CommAlgCat.{u} 𝕜) (x : (GL[n]).affinePoints R) :
    characterUnits F GL[n] det[n].toMul R x =
      Matrix.GeneralLinearGroup.det (affinePointsEquiv (Fin n) 𝕜 R x) := by
  let e := affinePointsEquiv (Fin n) 𝕜 R
  have hx := characterOnAffineMatrices_apply det[n].toMul R (e x)
  rw [MulEquiv.symm_apply_apply] at hx
  have h : characterOnAffineMatrices det[n].toMul R (e x) = Matrix.GeneralLinearGroup.det (e x) :=
    characterOnAffineMatrices_determinantCharacter (n := Fin n) R (e x)
  exact hx.symm.trans h

private theorem characterNorm_det (g : AdelicGroupPoints F GL[n]) :
    characterNorm F GL[n] det[n].toMul g = determinantNorm F n (adelicHomeomorph F n g) := by
  let R := CommAlgCat.of F (AdeleRing (𝓞 F) F)
  exact congrArg (IdeleAbsoluteValue.full F) (characterUnits_det F R g)

/-- The determinant norm and its reciprocal have polynomial growth in the
matrix-and-inverse height at every positive rank. -/
theorem determinantNorm_bounds (hn : 0 < n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ, ∀ g : AdelicGL F n,
      (((determinantNorm F n g : ℝ≥0) : ℝ) ≤ C * height F n g ^ e) ∧
      ((((determinantNorm F n g)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) ≤ C * height F n g ^ e := by
  have hclosed : IsClosedSubgroup std[n] := by
    change IsClosedImmersion (𝟙 (GL[n]).X.left)
    infer_instance
  obtain ⟨C, hC, e, h⟩ := exists_characterNorm_le F std[n] hn hclosed det[n]
  refine ⟨C, hC, e, fun g => ?_⟩
  have he := h ((adelicHomeomorph F n).symm g)
  simpa only [characterNorm_det, adelicHeight_standard, ContinuousMulEquiv.apply_symm_apply] using he

/-- The actual positive half of the block modulus has polynomial growth in
the product of the block heights. -/
theorem leviHalfCharacter_polynomialGrowth :
    (fun m : FullLevi F B => (leviHalfCharacter F B m : ℂ)) ∈
      polynomialGrowthAlgebra (blockProductHeight B F) (one_le_blockProductHeight B F) := by
  classical
  let H := blockProductHeight B F
  let A := polynomialGrowthAlgebra H (one_le_blockProductHeight B F)
  let f (i : Fin B.length) (m : FullLevi F B) := (((determinantNorm F (B.size i) (m i) : ℝ≥0) : ℝ) : ℂ)
  let g (i : Fin B.length) (m : FullLevi F B) :=
    (((((determinantNorm F (B.size i) (m i))⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ)
  have hfg (i : Fin B.length) : f i ∈ A ∧ g i ∈ A := by
    obtain ⟨C, hC, e, h⟩ := determinantNorm_bounds F (B.positive i)
    have hb (m : FullLevi F B) : C * height F (B.size i) (m i) ^ e ≤ C * H m ^ e :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (one_le_height F _ (B.positive i) _))
        (blockHeight_le_blockProductHeight B F m i) e) (zero_le_one.trans hC)
    refine ⟨⟨C, hC, e, fun m => ?_⟩, ⟨C, hC, e, fun m => ?_⟩⟩
    · simp only [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact (h (m i)).1.trans (hb m)
    · simp only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
      exact (h (m i)).2.trans (hb m)
  have hm : (fun m : FullLevi F B => (((leviCharacter F B m : ℝ≥0) : ℝ) : ℂ)) ∈ A := by
    have eq : (fun m : FullLevi F B => (((leviCharacter F B m : ℝ≥0) : ℝ) : ℂ)) =
        ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
          f i ^ B.size j * g j ^ B.size i := by
      funext m
      simp only [leviCharacter_apply, div_eq_mul_inv, Units.coe_prod,
        Units.val_mul, Units.val_pow_eq_pow_val, NNReal.coe_prod, NNReal.coe_mul, NNReal.coe_pow,
        Complex.ofReal_prod, Complex.ofReal_mul, Complex.ofReal_pow, f, g, Finset.prod_apply,
        Pi.mul_apply, Pi.pow_apply]
      simp only [Units.val_inv_eq_inv_val, NNReal.coe_inv, Complex.ofReal_inv, inv_pow]
      simp only [Units.val_pow_eq_pow_val, NNReal.coe_pow, Complex.ofReal_pow]
    rw [eq]
    exact A.prod_mem fun i _ => A.prod_mem fun j _ =>
      A.mul_mem (A.pow_mem (hfg i).1 _) (A.pow_mem (hfg j).2 _)
  obtain ⟨C, hC, e, h⟩ := hm
  refine ⟨C, hC, e, fun m => ?_⟩
  have hD : 1 ≤ C * H m ^ e :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (one_le_blockProductHeight B F m))
  have hu : ((leviCharacter F B m : ℝ≥0) : ℝ) ≤ C * H m ^ e := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using h m
  change ‖(leviHalfCharacter F B m : ℂ)‖ ≤ _
  rw [coe_leviHalfCharacter, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg _), Real.coe_sqrt]
  by_cases hl : ((leviCharacter F B m : ℝ≥0) : ℝ) ≤ 1
  · exact ((Real.sqrt_le_sqrt hl).trans_eq Real.sqrt_one).trans hD
  · exact (Real.sqrt_le_self_iff.mpr (Or.inr (le_of_not_ge hl))).trans hu

end AdelicMatrixHeight

end Langlands.Global
