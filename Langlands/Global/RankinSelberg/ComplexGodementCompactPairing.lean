import Langlands.Global.RankinSelberg.ComplexGodementCompactProjection
import Langlands.Global.RankinSelberg.ComplexGodementCompact
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Langlands.Representation.Archimedean.ComplexSwapJacquetDecay
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # A smaller standard vector with nonzero compact Godement pairing -/

noncomputable section

open MeasureTheory Matrix
open scoped Matrix.Norms.Operator Manifold

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGramFormula (phaseUnit phaseUnit_val)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (phaseMatrix phaseMatrix_val)
open Langlands.Archimedean.UnitaryFinitePolynomial (translateSpan)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "H" => Langlands.GeneralLinear n ℂ
local notation "G" => Langlands.GeneralLinear (n + 1) ℂ
local notation "K₀" => Matrix.unitaryGroup (Fin n) ℂ
local notation "K" => unitaryCompact ℂ (n + 1)
local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "Square" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
local notation "T" => (Fin n → Circle)

/-- The square matrix with `A` in the trailing block and `1` in the first diagonal position. -/
def trailingBlock : M →* Square where
  toFun A := Matrix.of fun i => Fin.cases (Fin.cons 1 0)
    (fun r => Fin.cons 0 (fun j => A r j)) i
  map_one' := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Matrix.one_apply, Ne.symm (Fin.succ_ne_zero _)]
  map_mul' A B := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ]

@[simp] theorem trailingBlock_zero_zero (A : M) : trailingBlock A 0 0 = 1 := rfl
@[simp] theorem trailingBlock_zero_succ (A : M) (j : Fin n) : trailingBlock A 0 j.succ = 0 := rfl
@[simp] theorem trailingBlock_succ_zero (A : M) (i : Fin n) : trailingBlock A i.succ 0 = 0 := rfl
@[simp] theorem trailingBlock_succ_succ (A : M) (i j : Fin n) : trailingBlock A i.succ j.succ = A i j := rfl

/-- The standard inclusion `h ↦ diag(1,h)` in the larger group. -/
def trailingBlockGL : H →* G := Units.map trailingBlock

@[simp] theorem trailingBlockGL_val (h : H) : (trailingBlockGL h).val = trailingBlock h.val := rfl

theorem trailingBlock_trailingRows (A : M) :
    trailingRows (trailingBlock A) = A * trailingRows (1 : Square) := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [trailingRows, Matrix.mul_apply, Fin.succ_ne_zero]
  · simp [trailingRows, Matrix.mul_apply, Matrix.one_apply, mul_ite]

private theorem trailingBlock_star (A : M) : trailingBlock (star A) = star (trailingBlock A) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.star_apply]

theorem determinant_trailingBlockGL (h : H) : determinant (trailingBlockGL h) = determinant h := by
  apply Units.ext
  change (trailingBlock h.val).det = h.val.det
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hsub : (trailingBlock h.val).submatrix Fin.succ Fin.succ = h.val := by
    ext i j
    simp [Matrix.submatrix_apply]
  simp [hsub]

theorem continuous_trailingBlockGL : Continuous (trailingBlockGL (n := n)) := by
  have hc : Continuous (trailingBlock (n := n)) := by
    apply continuous_matrix
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_id.matrix_elem _ _
  exact Units.continuous_iff.mpr ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩

theorem trailingBlockGL_mem_unitary {k : H} (hk : k ∈ unitaryCompact ℂ n) :
    trailingBlockGL k ∈ unitaryCompact ℂ (n + 1) := by
  change trailingBlock k.val ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ
  rw [Matrix.mem_unitaryGroup_iff, ← trailingBlock_star, ← map_mul,
    Unitary.mul_star_self_of_mem hk, map_one]

private theorem trailingBlock_diagonalUnits (z : Fin n → ℂˣ) :
    trailingBlockGL (diagonalUnits z) = diagonalUnits (Fin.cons 1 z) := by
  apply Units.ext
  rw [trailingBlockGL_val, diagonalUnits_val, diagonalUnits_val]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.diagonal_apply, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _)]

local instance compactPairingUnitaryMeasure (n : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  borel _
local instance compactPairingUnitaryBorel (n : ℕ) : BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩
local instance compactPairingTorusMeasure (n : ℕ) : MeasurableSpace (Fin n → Circle) := borel _
local instance compactPairingTorusBorel (n : ℕ) : BorelSpace (Fin n → Circle) := ⟨rfl⟩

/-- Normalized Haar measure on the compact matrix group used in the pairing. -/
def compactMatrixHaar (n : ℕ) : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤

instance compactMatrixHaar_probability (n : ℕ) : IsProbabilityMeasure (compactMatrixHaar n) :=
  ⟨by rw [← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
instance compactMatrixHaar_haar (n : ℕ) : (compactMatrixHaar n).IsHaarMeasure := by
  unfold compactMatrixHaar
  infer_instance
instance compactMatrixHaar_right (n : ℕ) : (compactMatrixHaar n).IsMulRightInvariant :=
  ⟨fun _ => Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩
instance compactMatrixHaar_left (n : ℕ) : (compactMatrixHaar n).IsMulLeftInvariant := by
  unfold compactMatrixHaar
  infer_instance

private def torusHaar (n : ℕ) : Measure (Fin n → Circle) := Measure.haarMeasure ⊤
private instance torusHaar_probability (n : ℕ) : IsProbabilityMeasure (torusHaar n) :=
  ⟨by rw [← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
private instance torusHaar_left (n : ℕ) : (torusHaar n).IsMulLeftInvariant := by
  unfold torusHaar
  infer_instance

private theorem phaseUnit_of_norm_one (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) : phaseUnit z = z := by
  apply Units.ext
  simp [phaseUnit_val, hz]

private theorem phaseUnit_norm (z : ℂˣ) : ‖(phaseUnit z : ℂˣ).val‖ = 1 := by
  rw [phaseUnit_val, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr z.ne_zero)]

private def phaseCircle (z : ℂˣ) : Circle :=
  ⟨(phaseUnit z).val, mem_sphere_zero_iff_norm.mpr (phaseUnit_norm z)⟩

private theorem circle_toUnits_phaseCircle (z : ℂˣ) : Circle.toUnits (phaseCircle z) = phaseUnit z := Units.ext rfl

private def diagonalCircle : T →* K₀ where
  toFun t := phaseMatrix fun i => Circle.toUnits (t i)
  map_one' := by simp [ComplexPrincipalSeriesExtension.phaseMatrix_one]
  map_mul' t s := by simp [ComplexPrincipalSeriesExtension.phaseMatrix_mul]

private theorem diagonalCircle_val (t : T) :
    (diagonalCircle t).val = Matrix.diagonal fun i => (t i : ℂ) := by
  rw [show (diagonalCircle t).val = (phaseMatrix (fun i => Circle.toUnits (t i))).val from rfl,
    phaseMatrix_val]
  congr 1
  funext i
  rw [phaseUnit_of_norm_one _ (Circle.norm_coe (t i))]
  rfl

private theorem continuous_diagonalCircle : Continuous (diagonalCircle (n := n)) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : T => (diagonalCircle t).val)
  simp_rw [diagonalCircle_val]
  apply continuous_matrix
  intro i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    exact continuous_subtype_val.comp (continuous_apply i : Continuous (fun t : T => t i))
  · simpa [hij] using (continuous_const : Continuous (fun _ : T => (0 : ℂ)))

private theorem continuous_circle_toUnits : Continuous Circle.toUnits := by
  apply Units.continuous_iff.mpr
  refine ⟨continuous_subtype_val, ?_⟩
  simp_rw [← map_inv]
  exact continuous_subtype_val.comp continuous_inv

private def torusCharacter (es : Fin n → ComplexCharacterData) : T →* ℂ where
  toFun t := ∏ i : Fin n, ((es i).character (Circle.toUnits (t i)) : ℂ)
  map_one' := by simp
  map_mul' t s := by simp [Finset.prod_mul_distrib]

private theorem continuous_torusCharacter (es : Fin n → ComplexCharacterData) :
    Continuous (torusCharacter es) := by
  change Continuous (fun t : T => ∏ i : Fin n, ((es i).character (Circle.toUnits (t i)) : ℂ))
  apply continuous_finsetProd
  intro i _
  exact Units.continuous_val.comp ((es i).character.continuous.comp
    (continuous_circle_toUnits.comp (continuous_apply i)))

private theorem torusCharacter_norm (es : Fin n → ComplexCharacterData) (t : T) : ‖torusCharacter es t‖ = 1 := by
  change ‖∏ i : Fin n, ((es i).character (Circle.toUnits (t i)) : ℂ)‖ = 1
  rw [norm_prod]
  simp [ComplexSwapJacquet.norm_character]

private theorem positionCharacter_ofFn : ∀ {m : ℕ} (es : Fin m → ComplexCharacterData)
    (j : Fin m) (z : ℂˣ), complexPositionCharacter (List.ofFn es) j z = ((es j).character z : ℂ)
  | 0, _, j, _ => j.elim0
  | m + 1, es, j, z => by
    rw [List.ofFn_succ]
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact positionCharacter_ofFn (fun r : Fin m => es r.succ) i z

private theorem principalSeriesCharacter_circle (es : Fin n → ComplexCharacterData) (t : T) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn es)) (fun i => Circle.toUnits (t i)) =
      torusCharacter es t := by
  simp [principalSeriesCharacter, positionCharacter_ofFn, torusCharacter]

private theorem principalSeriesCharacter_circle_cons (d : ComplexCharacterData)
    (es : Fin n → ComplexCharacterData) (t : T) :
    principalSeriesCharacter ℂ (n + 1) (complexPositionCharacter (d :: List.ofFn es))
      (Fin.cons 1 (fun i => Circle.toUnits (t i))) = torusCharacter es t := by
  rw [principalSeriesCharacter, Fin.prod_univ_succ]
  simp [complexPositionCharacter, positionCharacter_ofFn, torusCharacter]

/-- Restrict the larger inducing function along the embedded smaller compact group. -/
def compactTrailingRestriction : (G → ℂ) →ₗ[ℂ] (K₀ → ℂ) where
  toFun f k := f (trailingBlockGL (Unitary.toUnits k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem finiteDimensional_compactTrailingRestriction {f : G → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K) :
    FiniteDimensional ℂ (translateSpan (compactTrailingRestriction f)) := by
  rw [mem_kFiniteVectors_iff] at hf
  let V := Submodule.span ℂ (Set.range fun k : K => Whittaker.rightTranslation ℂ G k.val f)
  let : FiniteDimensional ℂ V := hf
  apply Submodule.finiteDimensional_of_le (S₂ := V.map compactTrailingRestriction)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let k' : K := ⟨trailingBlockGL (Unitary.toUnits k), trailingBlockGL_mem_unitary k.2⟩
  refine ⟨Whittaker.rightTranslation ℂ G k'.val f, Submodule.subset_span ⟨k', rfl⟩, ?_⟩
  funext x
  change f (trailingBlockGL (Unitary.toUnits x) * trailingBlockGL (Unitary.toUnits k)) =
    f (trailingBlockGL (Unitary.toUnits (x * k)))
  rw [map_mul, map_mul]

private theorem compactTrailingRestriction_circle {f : G → ℂ} (d : ComplexCharacterData)
    (es : Fin n → ComplexCharacterData) (hf : f ∈ complexStandardModule (n + 1) (d :: List.ofFn es))
    (t : T) : compactTrailingRestriction f (diagonalCircle t) = torusCharacter es t * compactTrailingRestriction f 1 := by
  have h₁ : Unitary.toUnits (diagonalCircle t) = diagonalUnits (fun i => Circle.toUnits (t i)) := by
    apply Units.ext
    rw [diagonalUnits_val]
    exact diagonalCircle_val t
  change f (trailingBlockGL (Unitary.toUnits (diagonalCircle t))) = _ * f (trailingBlockGL (Unitary.toUnits 1))
  rw [h₁, trailingBlock_diagonalUnits, map_one, map_one, ← principalSeriesCharacter_circle_cons d]
  simpa only [Subgroup.coe_one, mul_one] using hf.2 (Fin.cons 1 (fun i => Circle.toUnits (t i))) 1 1

/-- A compact-finite larger standard vector nonzero at `1` has a compact-finite smaller
standard vector with strictly positive real compact pairing along `diag(1,k)`. -/
def ComplexGodementCompactPairingStatement : Prop :=
  ∀ (d : ComplexCharacterData) (es : Fin n → ComplexCharacterData) (f : G → ℂ),
    f ∈ kFiniteFunctions (complexStandardModule (n + 1) (d :: List.ofFn es)) K → f 1 ≠ 0 →
    ∃ f₀ ∈ kFiniteFunctions (complexStandardModule n (List.ofFn es)) (unitaryCompact ℂ n),
      0 < (∫ k : K₀, f (trailingBlockGL (Unitary.toUnits k)) *
        f₀ (Unitary.toUnits k⁻¹) ∂compactMatrixHaar n).re

theorem complexGodementCompactPairing : ComplexGodementCompactPairingStatement (n := n) := by
  intro d es f hf hf₁
  have hfS : f ∈ complexStandardModule (n + 1) (d :: List.ofFn es) := hf.1
  obtain ⟨g, hgC, hgF, hgM, hgpos⟩ := complexGodementCompactProjection
    (torusHaar n) diagonalCircle (torusCharacter es) continuous_diagonalCircle (continuous_torusCharacter es)
    (torusCharacter_norm es) (compactMatrixHaar n) (compactTrailingRestriction f)
    (hfS.1.continuous.comp (continuous_trailingBlockGL.comp continuous_unitary_toUnits))
    (finiteDimensional_compactTrailingRestriction hf.2) (compactTrailingRestriction_circle d es hfS)
    (by simpa [compactTrailingRestriction] using hf₁)
  obtain ⟨f₀, hf₀, hrestr⟩ := complexPrincipalSeriesExtension n (List.ofFn es) g hgC hgF (fun a k => by
    let t : T := fun i => phaseCircle (a i)
    have ht : diagonalCircle t = phaseMatrix a := by
      apply Subtype.ext
      rw [diagonalCircle_val, phaseMatrix_val]
      rfl
    have h := hgM t k
    rw [ht, ← principalSeriesCharacter_circle] at h
    simpa only [t, circle_toUnits_phaseCircle] using h)
  refine ⟨f₀, hf₀, ?_⟩
  simpa only [hrestr, compactTrailingRestriction, LinearMap.coe_mk, AddHom.coe_mk] using hgpos

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
