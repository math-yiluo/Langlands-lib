import Langlands.Automorphic.ArchimedeanPlaceParameter
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Mathlib.Analysis.Complex.Circle

/-!
# The dual compact profile of an inverse-translation coefficient

Torus averaging of `k ↦ f(k⁻¹ x)` gives a compact profile for the inverse
inducing characters. It retains the value `f(x)` at the identity and the
compact pairing against each translated standard section.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Classical Matrix.Norms.Operator Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCompactDualProbe

open Langlands.Archimedean (complexPositionCharacter principalSeries principalSeriesCharacter unitaryCompact
  continuous_unitary_toUnits)
open Langlands.Archimedean.ComplexDuality (unitaryHaar)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit phaseUnit_val norm_phaseUnit complexPositionExponent)
open Langlands.Archimedean.ComplexPartialJacquet (dualChar)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (phaseMatrix phaseMatrix_val phaseMatrix_mul
  phaseMatrix_one extension extension_unitary contMDiff_extension extension_mul_left)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (complexPositionWeight complexPositionCharacter_phase isPhasePower)
open Langlands.Archimedean.GramFormula (shiftedExponent)
open Langlands.Archimedean.UnitaryFinitePolynomial (coord coordValue coord_apply polynomialFunctions separated
  inv_mul_mem_separated exists_mvPolynomial_of_mem_kFiniteVectors exists_mvPolynomial_of_mem_polynomialFunctions)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => Matrix.unitaryGroup (Fin n) ℂ
local notation "U" => unitaryCompact ℂ n
local notation "T" => Fin n → Circle
local notation "Std" => Automorphic.complexStandardKFinite n

local instance compactDualTorusMeasurable (n : ℕ) : MeasurableSpace (Fin n → Circle) := borel _
local instance compactDualTorusBorel (n : ℕ) : BorelSpace (Fin n → Circle) := ⟨rfl⟩

private def torusHaar (n : ℕ) : Measure (Fin n → Circle) := Measure.haarMeasure ⊤
private instance compactDualTorusHaarProbability (n : ℕ) : IsProbabilityMeasure (torusHaar n) :=
  ⟨by rw [← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
private instance compactDualTorusHaarLeft (n : ℕ) : (torusHaar n).IsMulLeftInvariant := by
  unfold torusHaar
  infer_instance

private def torusMatrix : T →* K where
  toFun t := phaseMatrix (fun i => Circle.toUnits (t i))
  map_one' := by simp [phaseMatrix_one]
  map_mul' t s := by simp [phaseMatrix_mul]

private theorem torusMatrix_val (t : T) : (torusMatrix t).val = Matrix.diagonal fun i => (t i : ℂ) := by
  change (phaseMatrix (fun i => Circle.toUnits (t i))).val = _
  rw [phaseMatrix_val]
  congr 1
  funext i
  rw [phaseUnit_val, show ‖((Circle.toUnits (t i) : ℂˣ) : ℂ)‖ = 1 from Circle.norm_coe (t i),
    Complex.ofReal_one, div_one]
  rfl

private theorem continuous_torusMatrix : Continuous (torusMatrix (n := n)) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : T => (torusMatrix t).val)
  simp_rw [torusMatrix_val]
  apply continuous_matrix
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    exact continuous_subtype_val.comp (continuous_apply i : Continuous (fun t : T => t i))
  · simpa [hij] using (continuous_const : Continuous (fun _ : T => (0 : ℂ)))

private def torusUnits (t : T) : U := ⟨Unitary.toUnits (torusMatrix t), (torusMatrix t).2⟩

private theorem torusUnits_val (t : T) :
    (torusUnits t).val = GeneralLinear.Iwasawa.diagonalUnits (fun i => Circle.toUnits (t i)) := by
  apply Units.ext
  change (torusMatrix t).val = _
  rw [torusMatrix_val, GeneralLinear.Iwasawa.diagonalUnits_val]
  rfl

private theorem continuous_torusUnits : Continuous (torusUnits (n := n)) :=
  (continuous_unitary_toUnits.comp continuous_torusMatrix).subtype_mk _

private def matrixOfCompact (k : U) : K := ⟨k.val.val, k.2⟩

private theorem toUnits_matrixOfCompact (k : U) : Unitary.toUnits (matrixOfCompact k) = k.val :=
  Units.ext rfl

private def angleCharacter (ds : List ComplexCharacterData) : T →* ℂ where
  toFun t := ∏ i : Fin n, (t i : ℂ) ^ complexPositionWeight ds i
  map_one' := by simp
  map_mul' t s := by simp only [Pi.mul_apply, Circle.coe_mul, mul_zpow, Finset.prod_mul_distrib]

private theorem norm_angleCharacter (ds : List ComplexCharacterData) (t : T) : ‖angleCharacter ds t‖ = 1 := by
  change ‖∏ i : Fin n, (t i : ℂ) ^ complexPositionWeight ds i‖ = 1
  simp [norm_prod, norm_zpow]

private theorem angleCharacter_ne_zero (ds : List ComplexCharacterData) (t : T) : angleCharacter ds t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_angleCharacter]
  exact one_ne_zero

private theorem continuous_angleCharacter (ds : List ComplexCharacterData) :
    Continuous (angleCharacter ds (n := n)) := by
  change Continuous (fun t : T => ∏ i : Fin n, (t i : ℂ) ^ complexPositionWeight ds i)
  refine continuous_finsetProd _ fun i _ => ?_
  have h : Continuous (fun t : T => (t i : ℂ)) := continuous_subtype_val.comp (continuous_apply i)
  exact h.zpow₀ _ (fun t => Or.inl (Circle.coe_ne_zero (t i)))

private theorem principalCharacter_torus (ds : List ComplexCharacterData) (t : T) :
    principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun i => Circle.toUnits (t i)) =
      angleCharacter ds t := by
  unfold principalSeriesCharacter angleCharacter
  refine Finset.prod_congr rfl fun i _ => ?_
  let z := Circle.toUnits (t i)
  have hz : ‖(z : ℂ)‖ = 1 := Circle.norm_coe _
  have hp : phaseUnit z = z := Units.ext (by simp [phaseUnit_val, hz])
  have hχ := complexPositionCharacter_phase ds (i : ℕ) z
  rw [hp] at hχ
  change complexPositionCharacter ds i z *
    ((‖(z : ℂ)‖ ^ Module.finrank ℝ ℂ : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - (i.val : ℂ)) =
    (z : ℂ) ^ complexPositionWeight ds i
  rw [hχ, hz, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]

private theorem principalDualCharacter_torus (ds : List ComplexCharacterData) (t : T) :
    principalSeriesCharacter ℂ n (dualChar (complexPositionCharacter ds)) (fun i => Circle.toUnits (t i)) =
      (angleCharacter ds t)⁻¹ := by
  have hz (i : Fin n) : ‖((Circle.toUnits (t i) : ℂˣ) : ℂ)‖ = 1 := Circle.norm_coe _
  rw [← principalCharacter_torus]
  simp only [principalSeriesCharacter, dualChar, hz, one_pow, Complex.ofReal_one, Complex.one_cpow,
    mul_one, Finset.prod_inv_distrib]

private theorem section_torus {ds : List ComplexCharacterData} (f : Std ds) (t : T) (y : G) :
    f.val ((torusUnits t).val * y) = angleCharacter ds t * f.val y := by
  rw [torusUnits_val, ← principalCharacter_torus]
  simpa only [Subgroup.coe_one, mul_one] using
    f.2.1.2 (fun i => Circle.toUnits (t i)) 1 y

private def angles (a : Fin n → ℂˣ) : T :=
  fun i => ⟨(phaseUnit (a i)).val, mem_sphere_zero_iff_norm.mpr (norm_phaseUnit (a i))⟩

private theorem circle_toUnits_angles (a : Fin n → ℂˣ) (i : Fin n) :
    Circle.toUnits (angles a i) = phaseUnit (a i) := Units.ext rfl

private theorem torusMatrix_angles (a : Fin n → ℂˣ) : torusMatrix (angles a) = phaseMatrix a := by
  apply Subtype.ext
  rw [torusMatrix_val, phaseMatrix_val]
  rfl

/-- The inverse-translation kernel projected to the dual inducing weight on the compact group. -/
def probe {ds : List ComplexCharacterData} (f : Std ds) (x k : K) : ℂ :=
  ∫ t : T, (angleCharacter ds t)⁻¹ * f.val (Unitary.toUnits (k⁻¹ * torusMatrix t * x)) ∂torusHaar n

/-- The value of the projected profile at the identity is the original evaluation at `x`. -/
theorem probe_one {ds : List ComplexCharacterData} (f : Std ds) (x : K) :
    probe f x 1 = f.val (Unitary.toUnits x) := by
  unfold probe
  simp_rw [inv_one, one_mul, map_mul, ← show ∀ t : T, (torusUnits t).val = Unitary.toUnits (torusMatrix t)
      from fun _ => rfl,
    section_torus f, ← mul_assoc, inv_mul_cancel₀ (angleCharacter_ne_zero ds _), one_mul]
  simp

theorem probe_covariance {ds : List ComplexCharacterData} (f : Std ds) (x k : K) (t : T) :
    probe f x (torusMatrix t * k) = (angleCharacter ds t)⁻¹ * probe f x k := by
  unfold probe
  conv_lhs => rw [← integral_mul_left_eq_self _ t]
  rw [← integral_const_mul]
  apply integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have h : (torusMatrix t * k)⁻¹ * torusMatrix (t * s) * x = k⁻¹ * torusMatrix s * x := by
    rw [map_mul]
    group
  rw [h, map_mul, mul_inv, mul_assoc]

/-- Averaging against the compact torus character preserves a uniform bound. -/
theorem norm_probe_le {ds : List ComplexCharacterData} (f : Std ds) (x k : K) {C : ℝ}
    (hC : ∀ y : K, ‖f.val (Unitary.toUnits y)‖ ≤ C) : ‖probe f x k‖ ≤ C := by
  unfold probe
  refine (norm_integral_le_of_norm_le_const (μ := torusHaar n) (C := C)
    (Filter.Eventually.of_forall fun t => ?_)).trans (by simp)
  rw [norm_mul, norm_inv, norm_angleCharacter, inv_one, one_mul]
  exact hC _

/-- A uniform bound on the compact translation difference also bounds the projected
profile's displacement from its identity value. -/
theorem norm_probe_sub_le {ds : List ComplexCharacterData} (f : Std ds) (x k : K) {C : ℝ}
    (hC : ∀ y : K, ‖f.val (Unitary.toUnits (k⁻¹ * y)) - f.val (Unitary.toUnits y)‖ ≤ C) :
    ‖probe f x k - f.val (Unitary.toUnits x)‖ ≤ C := by
  have hχ : Continuous (fun t : T => (angleCharacter ds t)⁻¹) :=
    (continuous_angleCharacter ds).inv₀ (angleCharacter_ne_zero ds)
  have h (l : K) : Integrable (fun t : T => (angleCharacter ds t)⁻¹ *
      f.val (Unitary.toUnits (l⁻¹ * torusMatrix t * x))) (torusHaar n) :=
    (hχ.mul (f.2.1.1.continuous.comp (continuous_unitary_toUnits.comp
      ((continuous_const.mul continuous_torusMatrix).mul continuous_const)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← probe_one f x]
  unfold probe
  rw [← integral_sub (h k) (h 1)]
  refine (norm_integral_le_of_norm_le_const (μ := torusHaar n) (C := C)
    (Filter.Eventually.of_forall fun t => ?_)).trans (by simp)
  simp only [inv_one, one_mul, ← mul_sub, norm_mul, norm_inv, norm_angleCharacter, mul_assoc]
  exact hC (torusMatrix t * x)

private theorem compactFunction_mem_adjoin {ds : List ComplexCharacterData} (f : Std ds) :
    (⟨fun k : K => f.val (Unitary.toUnits k), f.2.1.1.continuous.comp continuous_unitary_toUnits⟩ : C(K, ℂ)) ∈
      Algebra.adjoin ℂ (Set.range (coord n)) := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_kFiniteVectors f.2.1.1.continuous f.2.2 (1 : G)
  rw [Algebra.adjoin_range_eq_range_aeval]
  refine ⟨P, ?_⟩
  ext k
  have h := congrArg (fun φ => φ P)
    (MvPolynomial.comp_aeval (R := ℂ) (coord n) (ContinuousMap.evalAlgHom ℂ ℂ k))
  simp only [AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply] at h
  change ((MvPolynomial.aeval (coord n)) P) k = f.val (Unitary.toUnits k)
  rw [h, show (fun a => coord n a k) = coordValue k from funext fun a => coord_apply a k]
  simpa only [one_mul, MvPolynomial.aeval_eq_eval] using (hP k).symm

private theorem probe_polynomial {ds : List ComplexCharacterData} (f : Std ds) (x : K) :
    probe f x ∈ polynomialFunctions n := by
  let v : C(K, ℂ) := ⟨fun k => f.val (Unitary.toUnits k), f.2.1.1.continuous.comp continuous_unitary_toUnits⟩
  let w : T → ℂ := fun t => (angleCharacter ds t)⁻¹
  have hw : Continuous w := (continuous_angleCharacter ds).inv₀ (angleCharacter_ne_zero ds)
  let a : T → K := fun t => torusMatrix t * x
  have ha : Continuous a := continuous_torusMatrix.mul continuous_const
  have hsep : (fun y k => v (y⁻¹ * k)) ∈ separated n := inv_mul_mem_separated (compactFunction_mem_adjoin f)
  have hgen (H : K → K → ℂ) (hH : H ∈ separated n) :
      (∀ y, Continuous (H y)) ∧ (fun y => ∫ t, w t * H y (a t) ∂torusHaar n) ∈ polynomialFunctions n := by
    induction hH using Submodule.span_induction with
    | mem H hH =>
        obtain ⟨c, hc, b, rfl⟩ := hH
        refine ⟨fun y => continuous_const.mul b.continuous, ?_⟩
        have h : (fun y => ∫ t, w t * (c y * b (a t)) ∂torusHaar n) =
            (∫ t, w t * b (a t) ∂torusHaar n) • c := by
          funext y
          rw [Pi.smul_apply, smul_eq_mul, ← integral_mul_const]
          exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
        rw [h]
        exact Subalgebra.smul_mem _ hc _
    | zero =>
        refine ⟨fun _ => continuous_const, ?_⟩
        simp only [Pi.zero_apply, mul_zero, integral_zero]
        exact zero_mem _
    | add H J _ _ ihH ihJ =>
        refine ⟨fun y => (ihH.1 y).add (ihJ.1 y), ?_⟩
        have h (y : K) : (∫ t, w t * (H + J) y (a t) ∂torusHaar n) =
            (∫ t, w t * H y (a t) ∂torusHaar n) + ∫ t, w t * J y (a t) ∂torusHaar n := by
          simp only [Pi.add_apply, mul_add]
          exact integral_add ((hw.mul ((ihH.1 y).comp ha)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)) ((hw.mul ((ihJ.1 y).comp ha)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
        exact (funext h).symm ▸ add_mem ihH.2 ihJ.2
    | smul c H _ ih =>
        refine ⟨fun y => (ih.1 y).const_smul c, ?_⟩
        have h (y : K) : (∫ t, w t * (c • H) y (a t) ∂torusHaar n) =
            c * ∫ t, w t * H y (a t) ∂torusHaar n := by
          simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (w _)]
          exact integral_const_mul _ _
        exact (funext h).symm ▸ Subalgebra.smul_mem _ ih.2 c
  have h := (hgen _ hsep).2
  change (fun y : K => ∫ t : T, (angleCharacter ds t)⁻¹ *
    f.val (Unitary.toUnits (y⁻¹ * torusMatrix t * x)) ∂torusHaar n) ∈ polynomialFunctions n
  simpa only [v, ContinuousMap.coe_mk, w, a, mul_assoc] using h

/-- The smooth dual principal-series section of the averaged compact profile. -/
def dualSection {ds : List ComplexCharacterData} (f : Std ds) (x : K) : G → ℂ :=
  extension (shiftedExponent n (fun i => -complexPositionExponent ds i)) (probe f x)

theorem dualSection_mem {ds : List ComplexCharacterData} (f : Std ds) (x : K) :
    dualSection f x ∈ principalSeries ℂ n (dualChar (complexPositionCharacter ds)) := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions (probe_polynomial f x)
  refine ⟨contMDiff_extension _ hP, extension_mul_left _ (isPhasePower ds).dual.eq ?_⟩
  intro a k
  have h := probe_covariance f x k (angles a)
  rw [torusMatrix_angles, ← principalDualCharacter_torus] at h
  simpa only [circle_toUnits_angles] using h

theorem dualSection_unitary {ds : List ComplexCharacterData} (f : Std ds) (x k : K) :
    dualSection f x (Unitary.toUnits k) = probe f x k := extension_unitary _ _ _

private theorem compactIntegrand_eq {ds : List ComplexCharacterData} (f f₀ : Std ds) (x : K) (g : G) :
    (∫ k : U, probe f x (matrixOfCompact k) * f₀.val (k.val * g) ∂unitaryHaar n) =
      ∫ k : U, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g) ∂unitaryHaar n := by
  let H : U × T → ℂ := fun p => ((angleCharacter ds p.2)⁻¹ *
    f.val (p.1.val⁻¹ * (torusUnits p.2).val * Unitary.toUnits x)) * f₀.val (p.1.val * g)
  have hχ : Continuous (fun t : T => (angleCharacter ds t)⁻¹) :=
    (continuous_angleCharacter ds).inv₀ (angleCharacter_ne_zero ds)
  have hH : Continuous H := by
    refine ((hχ.comp continuous_snd).mul (f.2.1.1.continuous.comp ?_)).mul
      (f₀.2.1.1.continuous.comp ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
    exact (((continuous_subtype_val.comp continuous_fst).inv).mul
      (continuous_subtype_val.comp (continuous_torusUnits.comp continuous_snd))).mul continuous_const
  calc
    _ = ∫ k : U, ∫ t : T, H (k, t) ∂torusHaar n ∂unitaryHaar n := by
      simp only [H, integral_mul_const, probe, map_mul, map_inv, toUnits_matrixOfCompact, torusUnits]
    _ = ∫ t : T, ∫ k : U, H (k, t) ∂unitaryHaar n ∂torusHaar n :=
      integral_integral_swap_of_hasCompactSupport hH (HasCompactSupport.of_compactSpace _)
    _ = _ := by
      have ht (t : T) : (∫ k : U, H (k, t) ∂unitaryHaar n) =
          ∫ k : U, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g) ∂unitaryHaar n := by
        conv_lhs => rw [← integral_mul_left_eq_self _ (torusUnits t)]
        apply integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        have h₁ : ((torusUnits t * k : U).val⁻¹ * (torusUnits t).val * Unitary.toUnits x) =
            k.val⁻¹ * Unitary.toUnits x := by rw [Subgroup.coe_mul]; group
        have h₂ : (torusUnits t * k : U).val * g = (torusUnits t).val * (k.val * g) := by
          rw [Subgroup.coe_mul, mul_assoc]
        dsimp only [H]
        rw [h₁, h₂, section_torus f₀]
        rw [show (angleCharacter ds t)⁻¹ * f.val (k.val⁻¹ * Unitary.toUnits x) *
            (angleCharacter ds t * f₀.val (k.val * g)) =
            ((angleCharacter ds t)⁻¹ * angleCharacter ds t) *
              (f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g)) by ring,
          inv_mul_cancel₀ (angleCharacter_ne_zero ds t), one_mul]
      simp_rw [ht, integral_const, probReal_univ, one_smul]

/-- Dual compact extension preserves the inverse-translation pairing against a genuine
right translate of any compact-finite standard section. -/
def ComplexCompactDualProbeStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (f f₀ : Automorphic.complexStandardKFinite n ds)
    (x : Matrix.unitaryGroup (Fin n) ℂ) (g : Langlands.GeneralLinear n ℂ),
      dualSection f x ∈ principalSeries ℂ n (dualChar (complexPositionCharacter ds)) ∧
      dualSection f x 1 = f.val (Unitary.toUnits x) ∧
      (∫ k : unitaryCompact ℂ n, dualSection f x k.val * f₀.val (k.val * g) ∂unitaryHaar n) =
        ∫ k : unitaryCompact ℂ n, f.val (k.val⁻¹ * Unitary.toUnits x) * f₀.val (k.val * g) ∂unitaryHaar n

theorem complexCompactDualProbe : ComplexCompactDualProbeStatement := by
  intro n ds f f₀ x g
  refine ⟨dualSection_mem f x, ?_, ?_⟩
  · rw [← map_one (Unitary.toUnits : Matrix.unitaryGroup (Fin n) ℂ →* Langlands.GeneralLinear n ℂ),
      dualSection_unitary, probe_one]
  · have h (k : unitaryCompact ℂ n) : dualSection f x k.val = probe f x (matrixOfCompact k) := by
      rw [← toUnits_matrixOfCompact k, dualSection_unitary]
    simpa only [h] using compactIntegrand_eq f f₀ x g

end Langlands.Global.RankinSelbergGlobal.ComplexCompactDualProbe
