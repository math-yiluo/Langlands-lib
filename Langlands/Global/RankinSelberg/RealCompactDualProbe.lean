import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# The dual compact profile of an inverse-translation coefficient over the real field

Averaging `k ↦ f(k⁻¹ x)` over the finite group of diagonal sign matrices against the inverse
inducing character gives a compact profile for the inverse inducing characters. It retains the
value `f(x)` at the identity and the compact pairing against each translated standard section.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactDualProbe

open Langlands.Archimedean (realPositionCharacter principalSeries principalSeriesCharacter
  unitaryCompact continuous_unitary_toUnits)
open Langlands.Archimedean.GramFormula (signReal signUnit signUnit_val shiftedExponent
  realPositionExponent)
open Langlands.Archimedean.PartialJacquet (dualChar IsSignedPower)
open Langlands.Archimedean.PrincipalSeriesExtension (signDiagonal signDiagonal_mul extension
  extension_unitary contMDiff_extension extension_mul_left)
open Langlands.Archimedean.OrthogonalFinitePolynomial (entry entry_apply polynomialFunctions
  separated inv_mul_mem_separated exists_mvPolynomial_of_mem_kFiniteVectors
  exists_mvPolynomial_of_mem_polynomialFunctions)
open Langlands.Archimedean.RealPrincipalSeriesDuality (haarK)
open Langlands.LocalFactor.Archimedean (RealBlock)

local instance realCompactDualProbeKMeasurable (n : ℕ) :
    MeasurableSpace (unitaryCompact ℝ n) := borel _
local instance realCompactDualProbeKBorel (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "U" => unitaryCompact ℝ n
local notation "T" => Fin n → ℤˣ
local notation "Std" => Automorphic.realStandardKFinite n

/-- The inclusion of `±1` in the real units. -/
private def unitR : ℤˣ →* ℝˣ := Units.map (Int.castRingHom ℝ).toMonoidHom

private theorem unitR_val (t : ℤˣ) : ((unitR t : ℝˣ) : ℝ) = ((t : ℤ) : ℝ) := rfl

private theorem signReal_unitR (t : ℤˣ) : signReal ((unitR t : ℝˣ) : ℝ) = ((unitR t : ℝˣ) : ℝ) := by
  rcases Int.units_eq_one_or t with rfl | rfl <;> simp [unitR, signReal]

private theorem signUnit_unitR (t : ℤˣ) : signUnit (unitR t) = unitR t := by
  apply Units.ext
  rw [signUnit_val, signReal_unitR]

private theorem abs_unitR (t : ℤˣ) : |((unitR t : ℝˣ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or t with rfl | rfl <;> simp [unitR]

/-- The diagonal sign matrix of a sign vector. -/
private def signMat (t : T) : K := signDiagonal (fun i => ((unitR (t i) : ℝˣ) : ℝ))

private theorem signMat_val (t : T) :
    (signMat t : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal fun i => ((unitR (t i) : ℝˣ) : ℝ) := by
  change (Matrix.diagonal fun i => signReal ((unitR (t i) : ℝˣ) : ℝ)) = _
  simp only [signReal_unitR]

private theorem signMat_mul (t s : T) : signMat (t * s) = signMat t * signMat s := by
  unfold signMat
  rw [← signDiagonal_mul (fun i => (unitR (t i)).ne_zero) (fun i => (unitR (s i)).ne_zero)]
  congr 1
  funext i
  simp only [Pi.mul_apply, map_mul, Units.val_mul]

/-- The sign vector of a real unit vector. -/
private def toSign (a : Fin n → ℝˣ) : T := fun i => if (0 : ℝ) < (a i : ℝ) then 1 else -1

private theorem unitR_toSign (a : Fin n → ℝˣ) (i : Fin n) : unitR (toSign a i) = signUnit (a i) := by
  unfold toSign signUnit
  split_ifs <;> simp [unitR]

private theorem signDiagonal_eq_signMat (a : Fin n → ℝˣ) :
    signDiagonal (fun i => (a i : ℝ)) = signMat (toSign a) := by
  apply Subtype.ext
  rw [signMat_val]
  change (Matrix.diagonal fun i => signReal (a i : ℝ)) = _
  congr 1
  funext i
  rw [unitR_toSign, signUnit_val]

private theorem toUnits_signMat (t : T) :
    Unitary.toUnits (signMat t) =
      (Langlands.GeneralLinear.Iwasawa.diagonalUnits (fun i => unitR (t i)) : G) := by
  apply Units.ext
  change (signMat t : Matrix (Fin n) (Fin n) ℝ) = _
  rw [signMat_val, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]

/-- The character of the sign vector. -/
private def signCharacter (ds : List RealBlock) (t : T) : ℂ :=
  principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => unitR (t i))

private theorem signCharacter_mul (ds : List RealBlock) (t s : T) :
    signCharacter ds (t * s) = signCharacter ds t * signCharacter ds s := by
  have hχ := Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.isSignedPower ds
  unfold signCharacter principalSeriesCharacter
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.mul_apply, map_mul, Units.val_mul, norm_mul, Real.norm_eq_abs, abs_unitR,
    one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  have hm : unitR (-1) * unitR (-1) = 1 := by ext; simp [unitR]
  rcases Int.units_eq_one_or (t i) with h | h <;> rcases Int.units_eq_one_or (s i) with h' | h' <;>
    simp only [h, h', map_one, one_mul, mul_one, hχ.one, hm]
  rw [show unitR (-1) = -1 from by ext; simp [unitR]]
  rcases Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.realPositionCharacter_neg_one
    ds i with h₁ | h₁ <;> simp [h₁]

private theorem norm_signCharacter (ds : List RealBlock) (t : T) : ‖signCharacter ds t‖ = 1 := by
  have hχ := Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.isSignedPower ds
  unfold signCharacter principalSeriesCharacter
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [norm_mul]
  have h1 : ‖realPositionCharacter ds i (unitR (t i))‖ = 1 := by
    rcases Int.units_eq_one_or (t i) with h | h
    · simp [h, hχ.one]
    · rw [h, show unitR (-1) = -1 from by ext; simp [unitR]]
      exact hχ.norm_neg_one i
  rw [h1, one_mul, Real.norm_eq_abs, abs_unitR]
  simp

private theorem signCharacter_ne_zero (ds : List RealBlock) (t : T) : signCharacter ds t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_signCharacter]
  exact one_ne_zero

private theorem section_sign {ds : List RealBlock} (f : Std ds) (t : T) (y : G) :
    f.val (Unitary.toUnits (signMat t) * y) = signCharacter ds t * f.val y := by
  rw [toUnits_signMat]
  have h := f.2.1.1.2 (fun i => unitR (t i)) 1 y
  simpa only [Subgroup.coe_one, mul_one, signCharacter] using h

private theorem dualCharacter_sign (ds : List RealBlock) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (dualChar (realPositionCharacter ds)) (fun i => signUnit (a i)) =
      (signCharacter ds (toSign a))⁻¹ := by
  unfold signCharacter principalSeriesCharacter dualChar
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [unitR_toSign]
  have habs : ‖((signUnit (a i) : ℝˣ) : ℝ)‖ = 1 := by
    rw [signUnit_val, Real.norm_eq_abs]
    unfold signReal
    split_ifs <;> simp
  simp only [habs, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]

private def card : ℂ := (Fintype.card T : ℂ)

private theorem card_ne_zero : (card (n := n)) ≠ 0 := by
  unfold card
  exact_mod_cast Fintype.card_ne_zero

/-- The inverse-translation kernel projected to the dual inducing signs on the compact group. -/
def probe {ds : List RealBlock} (f : Std ds) (x k : K) : ℂ :=
  (card (n := n))⁻¹ * ∑ t : T, (signCharacter ds t)⁻¹ * f.val (Unitary.toUnits (k⁻¹ * signMat t * x))

/-- The value of the projected profile at the identity is the original evaluation at `x`. -/
theorem probe_one {ds : List RealBlock} (f : Std ds) (x : K) :
    probe f x 1 = f.val (Unitary.toUnits x) := by
  unfold probe
  have h (t : T) : (signCharacter ds t)⁻¹ * f.val (Unitary.toUnits (1⁻¹ * signMat t * x)) =
      f.val (Unitary.toUnits x) := by
    rw [inv_one, one_mul, map_mul, section_sign, ← mul_assoc,
      inv_mul_cancel₀ (signCharacter_ne_zero ds t), one_mul]
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold card
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

theorem probe_covariance {ds : List RealBlock} (f : Std ds) (x k : K) (t : T) :
    probe f x (signMat t * k) = (signCharacter ds t)⁻¹ * probe f x k := by
  unfold probe
  have hsum : (∑ s : T, (signCharacter ds s)⁻¹ *
        f.val (Unitary.toUnits ((signMat t * k)⁻¹ * signMat s * x))) =
      (signCharacter ds t)⁻¹ * ∑ s : T, (signCharacter ds s)⁻¹ *
        f.val (Unitary.toUnits (k⁻¹ * signMat s * x)) := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft t)
      (fun s => (signCharacter ds t)⁻¹ * ((signCharacter ds s)⁻¹ *
        f.val (Unitary.toUnits (k⁻¹ * signMat s * x))))
      (fun s => (signCharacter ds s)⁻¹ *
        f.val (Unitary.toUnits ((signMat t * k)⁻¹ * signMat s * x))) fun s => ?_).symm
    change _ = (signCharacter ds (t * s))⁻¹ *
      f.val (Unitary.toUnits ((signMat t * k)⁻¹ * signMat (t * s) * x))
    have hk : (signMat t * k)⁻¹ * signMat (t * s) * x = k⁻¹ * signMat s * x := by
      rw [signMat_mul]
      group
    rw [hk, signCharacter_mul, mul_inv]
    ring
  rw [hsum, mul_left_comm]

/-- Averaging against the sign characters preserves a uniform bound. -/
theorem norm_probe_le {ds : List RealBlock} (f : Std ds) (x k : K) {C : ℝ}
    (hC : ∀ y : K, ‖f.val (Unitary.toUnits y)‖ ≤ C) : ‖probe f x k‖ ≤ C := by
  unfold probe
  rw [norm_mul, norm_inv]
  have hcard : ‖(card (n := n))‖ = (Fintype.card T : ℝ) := by
    unfold card; simp
  rw [hcard]
  have hpos : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [inv_mul_le_iff₀ hpos]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _t : T, (C : ℝ) := Finset.sum_le_sum fun t _ => by
      rw [norm_mul, norm_inv, norm_signCharacter, inv_one, one_mul]
      exact hC _
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- A uniform bound on the compact translation difference also bounds the projected
profile's displacement from its identity value. -/
theorem norm_probe_sub_le {ds : List RealBlock} (f : Std ds) (x k : K) {C : ℝ}
    (hC : ∀ y : K, ‖f.val (Unitary.toUnits (k⁻¹ * y)) - f.val (Unitary.toUnits y)‖ ≤ C) :
    ‖probe f x k - f.val (Unitary.toUnits x)‖ ≤ C := by
  rw [← probe_one f x]
  unfold probe
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv]
  have hcard : ‖(card (n := n))‖ = (Fintype.card T : ℝ) := by
    unfold card; simp
  rw [hcard]
  have hpos : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [inv_mul_le_iff₀ hpos]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _t : T, (C : ℝ) := Finset.sum_le_sum fun t _ => by
      rw [inv_one, one_mul, ← mul_sub, norm_mul, norm_inv, norm_signCharacter, inv_one, one_mul,
        mul_assoc]
      exact hC (signMat t * x)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

private theorem compactFunction_mem_adjoin {ds : List RealBlock} (f : Std ds) :
    (⟨fun k : K => f.val (Unitary.toUnits k),
      f.2.1.1.1.continuous.comp continuous_unitary_toUnits⟩ : C(K, ℂ)) ∈
      Algebra.adjoin ℂ (Set.range (entry n)) := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_kFiniteVectors f.2.1.1.1.continuous f.2.2 (1 : G)
  rw [Algebra.adjoin_range_eq_range_aeval]
  refine ⟨P, ?_⟩
  ext k
  have h := congrArg (fun φ => φ P)
    (MvPolynomial.comp_aeval (R := ℂ) (entry n) (ContinuousMap.evalAlgHom ℂ ℂ k))
  simp only [AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply] at h
  change ((MvPolynomial.aeval (entry n)) P) k = f.val (Unitary.toUnits k)
  rw [h, show (fun a => entry n a k) = (fun ij => ((k : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ))
    from funext fun a => entry_apply a k]
  simpa only [one_mul, MvPolynomial.aeval_eq_eval] using (hP k).symm

private theorem probe_polynomial {ds : List RealBlock} (f : Std ds) (x : K) :
    probe f x ∈ polynomialFunctions n := by
  let v : C(K, ℂ) := ⟨fun k => f.val (Unitary.toUnits k),
    f.2.1.1.1.continuous.comp continuous_unitary_toUnits⟩
  have hsep : (fun y k => v (y⁻¹ * k)) ∈ separated n :=
    inv_mul_mem_separated (compactFunction_mem_adjoin f)
  have hgen (H : K → K → ℂ) (hH : H ∈ separated n) (b : K) :
      (fun y => H y b) ∈ polynomialFunctions n := by
    induction hH using Submodule.span_induction with
    | mem H hH =>
        obtain ⟨c, hc, β, rfl⟩ := hH
        have h : (fun y => c y * β b) = β b • c := by
          funext y; rw [Pi.smul_apply, smul_eq_mul, mul_comm]
        rw [h]
        exact Subalgebra.smul_mem _ hc _
    | zero => exact zero_mem _
    | add H J _ _ ihH ihJ => exact add_mem ihH ihJ
    | smul c H _ ih =>
        have h : (fun y => (c • H) y b) = c • fun y => H y b := rfl
        rw [h]
        exact Subalgebra.smul_mem _ ih c
  have h : probe f x = (card (n := n))⁻¹ • ∑ t : T, (signCharacter ds t)⁻¹ •
      (fun y => v (y⁻¹ * (signMat t * x))) := by
    funext y
    simp only [probe, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, v, ContinuousMap.coe_mk,
      mul_assoc]
  rw [h]
  exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun t _ =>
    Subalgebra.smul_mem _ (hgen _ hsep (signMat t * x)) _) _

/-- The smooth dual principal-series section of the averaged compact profile. -/
def dualSection {ds : List RealBlock} (f : Std ds) (x : K) : G → ℂ :=
  extension (shiftedExponent n (fun l => -realPositionExponent ds l)) (probe f x)

theorem dualSection_mem {ds : List RealBlock} (f : Std ds) (x : K) :
    dualSection f x ∈ principalSeries ℝ n (dualChar (realPositionCharacter ds)) := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions (probe_polynomial f x)
  have hχ := (Langlands.Archimedean.RealStrictCharacterLanglandsQuotient.isSignedPower ds).dual
  refine ⟨contMDiff_extension _ hP, extension_mul_left _ hχ.eq ?_⟩
  intro a k
  rw [signDiagonal_eq_signMat, probe_covariance, dualCharacter_sign]

theorem dualSection_unitary {ds : List RealBlock} (f : Std ds) (x k : K) :
    dualSection f x (Unitary.toUnits k) = probe f x k := extension_unitary _ _ _

private def matrixOfCompact (k : U) : K := ⟨k.val.val, k.2⟩

private theorem toUnits_matrixOfCompact (k : U) : Unitary.toUnits (matrixOfCompact k) = k.val :=
  Units.ext rfl

private def signUnits (t : T) : U := ⟨Unitary.toUnits (signMat t), (signMat t).2⟩

private theorem compactIntegrand_eq {ds : List RealBlock} (f f₀ : Std ds) (x : K) (g : G) :
    (∫ k : U, probe f x (matrixOfCompact k) * f₀.val (k.val * g) ∂haarK n) =
      ∫ k : U, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g) ∂haarK n := by
  have hcont (t : T) : Continuous (fun k : U =>
      ((signCharacter ds t)⁻¹ * f.val (k.val⁻¹ * (signUnits t).val * Unitary.toUnits x)) *
        f₀.val (k.val * g)) :=
    (continuous_const.mul (f.2.1.1.1.continuous.comp
      (((continuous_subtype_val.inv).mul continuous_const).mul continuous_const))).mul
      (f₀.2.1.1.1.continuous.comp (continuous_subtype_val.mul continuous_const))
  have ht (t : T) : (∫ k : U, ((signCharacter ds t)⁻¹ *
      f.val (k.val⁻¹ * (signUnits t).val * Unitary.toUnits x)) * f₀.val (k.val * g) ∂haarK n) =
      ∫ k : U, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g) ∂haarK n := by
    conv_lhs => rw [← integral_mul_left_eq_self _ (signUnits t)]
    apply integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have h₁ : ((signUnits t * k : U).val⁻¹ * (signUnits t).val * Unitary.toUnits x) =
        k.val⁻¹ * Unitary.toUnits x := by rw [Subgroup.coe_mul]; group
    have h₂ : (signUnits t * k : U).val * g = (signUnits t).val * (k.val * g) := by
      rw [Subgroup.coe_mul, mul_assoc]
    rw [h₁, h₂, show (signUnits t).val = Unitary.toUnits (signMat t) from rfl, section_sign f₀]
    rw [show (signCharacter ds t)⁻¹ * f.val (k.val⁻¹ * Unitary.toUnits x) *
        (signCharacter ds t * f₀.val (k.val * g)) =
        ((signCharacter ds t)⁻¹ * signCharacter ds t) *
          (f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g)) by ring,
      inv_mul_cancel₀ (signCharacter_ne_zero ds t), one_mul]
  calc
    _ = ∫ k : U, (card (n := n))⁻¹ * ∑ t : T, ((signCharacter ds t)⁻¹ *
          f.val (k.val⁻¹ * (signUnits t).val * Unitary.toUnits x)) * f₀.val (k.val * g)
          ∂haarK n := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      have hk (t : T) : f.val (Unitary.toUnits ((matrixOfCompact k)⁻¹ * (signMat t * x))) =
          f.val (k.val⁻¹ * ((signUnits t).val * Unitary.toUnits x)) := by
        rw [map_mul, map_mul, map_inv, toUnits_matrixOfCompact]
        rfl
      simp only [probe, Finset.sum_mul, mul_assoc, hk]
    _ = (card (n := n))⁻¹ * ∑ t : T, ∫ k : U, ((signCharacter ds t)⁻¹ *
          f.val (k.val⁻¹ * (signUnits t).val * Unitary.toUnits x)) * f₀.val (k.val * g)
          ∂haarK n := by
      rw [integral_const_mul, integral_finsetSum]
      intro t _
      exact (hcont t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    _ = _ := by
      simp_rw [ht]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold card
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

/-- Dual compact extension preserves the inverse-translation pairing against a genuine
right translate of any compact-finite standard section. -/
def RealCompactDualProbeStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (f f₀ : Automorphic.realStandardKFinite n ds)
    (x : Matrix.unitaryGroup (Fin n) ℝ) (g : Langlands.GeneralLinear n ℝ),
      dualSection f x ∈ principalSeries ℝ n (dualChar (realPositionCharacter ds)) ∧
      dualSection f x 1 = f.val (Unitary.toUnits x) ∧
      (∫ k : unitaryCompact ℝ n, dualSection f x k.val * f₀.val (k.val * g) ∂haarK n) =
        ∫ k : unitaryCompact ℝ n, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g)
          ∂haarK n

theorem realCompactDualProbe : RealCompactDualProbeStatement := by
  intro n ds f f₀ x g
  refine ⟨dualSection_mem f x, ?_, ?_⟩
  · rw [← map_one (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℝ →* Langlands.GeneralLinear n ℝ),
      dualSection_unitary, probe_one]
  · have h (k : unitaryCompact ℝ n) : dualSection f x k.val = probe f x (matrixOfCompact k) := by
      rw [← toUnits_matrixOfCompact k, dualSection_unitary]
    simpa only [h] using compactIntegrand_eq f f₀ x g

end Langlands.Global.RankinSelbergGlobal.RealCompactDualProbe
