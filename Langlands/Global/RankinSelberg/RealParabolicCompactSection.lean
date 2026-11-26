import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Maps.Proper.Basic

/-! # Smooth compact rectangle sections in the real parabolic cell -/

noncomputable section

open Filter Matrix Set
open scoped ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.GeneralLinear Langlands.Archimedean

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "M" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "X" => fun m n => Matrix (Fin m) (Fin n) ℝ

variable {m n : ℕ}

/-- A real matrix in consecutive two-block coordinates. -/
def split (g : M (m + n)) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  g.submatrix finSumFinEquiv finSumFinEquiv

private abbrev lead (g : M (m + n)) : M m := (split g).toBlocks₁₁
private abbrev upper (g : M (m + n)) : X m n := (split g).toBlocks₁₂
private abbrev lower (g : M (m + n)) : X n m := (split g).toBlocks₂₁
private abbrev tail (g : M (m + n)) : M n := (split g).toBlocks₂₂

private def rectangle (g : M (m + n)) : X m n := Ring.inverse (lead g) * upper g
private def schur (g : M (m + n)) : M n := tail g - lower g * rectangle g

/-- The open cell where the leading pivot is invertible. -/
def parabolicCell (m n : ℕ) : Set (G (m + n)) := {g | (lead g.val).det ≠ 0}

/-- The complex determinant power with the real positive logarithm. -/
def detWeight {d : ℕ} (z : ℂ) (A : M d) : ℂ := Complex.exp (z * (Real.log |A.det| : ℂ))

private theorem detWeight_contDiffAt {d : ℕ} (z : ℂ) (A : M d) (hA : A.det ≠ 0) :
    ContDiffAt ℝ ∞ (detWeight z) A := by
  have hdet : ContDiff ℝ ∞ (Matrix.det : M d → ℝ) := by
    apply PrincipalSeriesExtension.contDiff_det_comp
    exact PrincipalSeriesExtension.contDiff_entry
  have habs := hdet.contDiffAt.abs hA
  exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp A
    (habs.log (abs_ne_zero.mpr hA)))).cexp

private def submatrixCLM {d a b : ℕ} (i : Fin a → Fin d) (j : Fin b → Fin d) :
    M d →L[ℝ] X a b :=
  (show M d →ₗ[ℝ] X a b from {
    toFun := fun g => g.submatrix i j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }).toContinuousLinearMap

private theorem contDiff_lead : ContDiff ℝ ∞ (lead (m := m) (n := n)) :=
  (submatrixCLM (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inl i))).contDiff

private theorem contDiff_upper : ContDiff ℝ ∞ (upper (m := m) (n := n)) :=
  (submatrixCLM (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inr i))).contDiff

private theorem contDiff_lower : ContDiff ℝ ∞ (lower (m := m) (n := n)) :=
  (submatrixCLM (fun i => finSumFinEquiv (Sum.inr i)) (fun i => finSumFinEquiv (Sum.inl i))).contDiff

private theorem contDiff_tail : ContDiff ℝ ∞ (tail (m := m) (n := n)) :=
  (submatrixCLM (fun i => finSumFinEquiv (Sum.inr i)) (fun i => finSumFinEquiv (Sum.inr i))).contDiff

private theorem contDiffAt_matrix_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : ℕ} {f : E → X a b} {g : E → X b c} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => f y * g y) x := by
  let assemble : (Fin a → Fin c → ℝ) →L[ℝ] X a c :=
    (Matrix.ofLinearEquiv ℝ).toLinearMap.toContinuousLinearMap
  have he : ContDiffAt ℝ ∞ (fun y : E => fun i j => (f y * g y) i j) x := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    simp only [Matrix.mul_apply]
    exact ContDiffAt.sum fun k _ =>
      ((Matrix.entryLinearMap ℝ ℝ i k).toContinuousLinearMap.contDiff.contDiffAt.comp x hf).mul
        ((Matrix.entryLinearMap ℝ ℝ k j).toContinuousLinearMap.contDiff.contDiffAt.comp x hg)
  exact assemble.contDiff.contDiffAt.comp x he

private theorem contDiffAt_rectangle (g : M (m + n)) (h : IsUnit (lead g)) :
    ContDiffAt ℝ ∞ rectangle g := by
  have hInv : ContDiffAt ℝ ∞ Ring.inverse (lead g) := by
    rw [← h.unit_spec]
    exact contDiffAt_ringInverse ℝ h.unit
  exact contDiffAt_matrix_mul (hInv.comp g contDiff_lead.contDiffAt) contDiff_upper.contDiffAt

private theorem lead_mul_rectangle (g : M (m + n)) (h : IsUnit (lead g)) :
    lead g * rectangle g = upper g := by
  rw [rectangle, ← Matrix.mul_assoc, ← h.unit_spec, Ring.inverse_unit]
  have hu : h.unit.val * h.unit⁻¹.val = 1 := h.unit.val_inv
  rw [hu, Matrix.one_mul]

private theorem det_of_upper_eq (g : M (m + n)) (Y : X m n) (hY : upper g = lead g * Y) :
    g.det = (lead g).det * (tail g - lower g * Y).det := by
  let T : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ := Matrix.fromBlocks 1 (-Y) 0 1
  have hT : T.det = 1 := by simp [T]
  have he : split g * T = Matrix.fromBlocks (lead g) 0 (lower g) (tail g - lower g * Y) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (split g)]
    dsimp only [T]
    change (split g).toBlocks₁₂ = (split g).toBlocks₁₁ * Y at hY
    rw [Matrix.fromBlocks_multiply, hY]
    simp [sub_eq_add_neg, add_comm]
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, hT, mul_one, Matrix.det_fromBlocks_zero₁₂] at hd
  simpa only [split, Matrix.det_submatrix_equiv_self] using hd

private theorem det_schur_ne_zero (g : G (m + n)) (h : IsUnit (lead g.val)) :
    (schur g.val).det ≠ 0 := by
  have hd := det_of_upper_eq g.val (rectangle g.val) (lead_mul_rectangle g.val h).symm
  have hne : g.val.det ≠ 0 := (determinant g).ne_zero
  rw [hd] at hne
  exact (mul_ne_zero_iff.mp hne).2

private def sectionFormula (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ) (φ : X m n → ℂ)
    (u : M (m + n)) : ℂ :=
  detWeight z₁ (lead u) * detWeight z₂ (schur u) *
    unitsExtension f (lead u) * unitsExtension g (schur u) * φ (rectangle u)

/-- The section given by the two invertible Levi arguments on the open cell, and zero elsewhere. -/
def compactSection (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ) (φ : X m n → ℂ)
    (u : G (m + n)) : ℂ := by
  classical
  exact if u ∈ parabolicCell m n then sectionFormula z₁ z₂ f g φ u.val else 0

private theorem isOpen_cell : IsOpen (parabolicCell m n) :=
  isOpen_ne.preimage (contDiff_lead.continuous.comp
    (Units.continuous_val : Continuous (fun u : G (m + n) => u.val))).matrix_det

private theorem isClosed_rectangleSupport (K : Set (X m n)) (hK : IsCompact K) :
    IsClosed {u : G (m + n) | ∃ Y ∈ K, upper u.val = lead u.val * Y} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hu : Continuous (fun u : G (m + n) => u.val) := Units.continuous_val
  have h₁ : Continuous (fun p : G (m + n) × K => upper p.1.val) :=
    contDiff_upper.continuous.comp (hu.comp continuous_fst)
  have h₂ : Continuous (fun p : G (m + n) × K => lead p.1.val * p.2.val) :=
    (contDiff_lead.continuous.comp (hu.comp continuous_fst)).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  have hc := isClosedMap_fst_of_compactSpace _ (isClosed_eq h₁ h₂)
  have he : (Prod.fst '' {p : G (m + n) × K | upper p.1.val = lead p.1.val * p.2.val}) =
      {u : G (m + n) | ∃ Y ∈ K, upper u.val = lead u.val * Y} := by
    ext u
    constructor
    · rintro ⟨⟨v, ⟨Y, hY⟩⟩, he, rfl⟩
      exact ⟨Y, hY, he⟩
    · rintro ⟨Y, hY, he⟩
      exact ⟨(u, ⟨Y, hY⟩), he, rfl⟩
  exact he ▸ hc

private theorem rectangleSupport_subset_cell (K : Set (X m n)) :
    {u : G (m + n) | ∃ Y ∈ K, upper u.val = lead u.val * Y} ⊆ parabolicCell m n := by
  rintro u ⟨Y, _, hY⟩
  have hd := det_of_upper_eq u.val Y hY
  have hne : u.val.det ≠ 0 := (determinant u).ne_zero
  rw [hd] at hne
  exact (mul_ne_zero_iff.mp hne).1

private theorem tsupport_compactSection_subset (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (φ : X m n → ℂ) (hφ : HasCompactSupport φ) :
    tsupport (compactSection z₁ z₂ f g φ) ⊆ {u : G (m + n) | ∃ Y ∈ tsupport φ, upper u.val = lead u.val * Y} := by
  apply closure_minimal _ (isClosed_rectangleSupport (tsupport φ) hφ)
  intro u hu
  by_cases hc : u ∈ parabolicCell m n
  · have h : IsUnit (lead u.val) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hc)
    have hφ' : rectangle u.val ∈ Function.support φ := by
      intro hz
      exact hu (by simp [compactSection, hc, sectionFormula, hz])
    exact ⟨rectangle u.val, subset_tsupport _ hφ', (lead_mul_rectangle u.val h).symm⟩
  · exact False.elim (hu (by simp [compactSection, hc]))

set_option maxHeartbeats 1000000 in
private theorem contMDiff_compactSection (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (φ : X m n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hφC : HasCompactSupport φ) :
    ContMDiff (matrixModel ℝ (m + n)) 𝓘(ℝ, ℂ) ∞ (compactSection z₁ z₂ f g φ) := by
  intro u
  by_cases hu : u ∈ parabolicCell m n
  · have hA : IsUnit (lead u.val) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hu)
    have hS₀ := det_schur_ne_zero u hA
    have hS : IsUnit (schur u.val) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hS₀)
    have hY := contDiffAt_rectangle u.val hA
    have hD : ContDiffAt ℝ ∞ schur u.val :=
      contDiff_tail.contDiffAt.sub (contDiffAt_matrix_mul contDiff_lower.contDiffAt hY)
    have hF := ((contDiffOn_unitsExtension hf).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds hA)).comp u.val contDiff_lead.contDiffAt
    have hG := ((contDiffOn_unitsExtension hg).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds hS)).comp u.val hD
    have hW₁ := (detWeight_contDiffAt z₁ (lead u.val) hu).comp u.val contDiff_lead.contDiffAt
    have hW₂ := (detWeight_contDiffAt z₂ (schur u.val) hS₀).comp u.val hD
    have hForm : ContDiffAt ℝ ∞ (sectionFormula z₁ z₂ f g φ) u.val :=
      (((hW₁.mul hW₂).mul hF).mul hG).mul (hφ.contDiffAt.comp u.val hY)
    have hVal : ContMDiffAt (matrixModel ℝ (m + n)) 𝓘(ℝ, M (m + n)) ∞ Units.val u :=
      Units.contMDiff_val u
    refine (hForm.comp_contMDiffAt hVal).congr_of_eventuallyEq ?_
    have he : ∀ᶠ v in 𝓝 u, v ∈ parabolicCell m n := isOpen_cell.mem_nhds hu
    exact he.mono fun v hv => ite_eq_left hv
  · have hS : tsupport (compactSection z₁ z₂ f g φ) ⊆ parabolicCell m n :=
      (tsupport_compactSection_subset z₁ z₂ f g φ hφC).trans (rectangleSupport_subset_cell _)
    have hc : IsClosed (tsupport (compactSection z₁ z₂ f g φ)) := isClosed_closure
    have he : ∀ᶠ v in 𝓝 u, v ∉ tsupport (compactSection z₁ z₂ f g φ) :=
      hc.isOpen_compl.mem_nhds (fun hs => hu (hS hs))
    exact contMDiffAt_const.congr_of_eventuallyEq (he.mono fun v hv =>
      Function.notMem_support.mp fun hv' => hv (subset_tsupport _ hv'))

private theorem compactSection_of_split (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (φ : X m n → ℂ) (u : G (m + n)) (a : G m) (b : G n) (C : X n m) (Y : X m n)
    (hu : split u.val = Matrix.fromBlocks a.val (a.val * Y) C (C * Y + b.val)) :
    compactSection z₁ z₂ f g φ u = detWeight z₁ a.val * detWeight z₂ b.val * f a * g b * φ Y := by
  have hA : lead u.val = a.val := by simp only [lead, hu, Matrix.toBlocks_fromBlocks₁₁]
  have hY : rectangle u.val = Y := by
    rw [rectangle, hA]
    simp only [upper, hu, Matrix.toBlocks_fromBlocks₁₂, Ring.inverse_unit, ← Matrix.mul_assoc]
    have ha : a⁻¹.val * a.val = 1 := a.inv_val
    rw [ha, Matrix.one_mul]
  have hS : schur u.val = b.val := by
    simp only [schur, hY, tail, lower, hu, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.toBlocks_fromBlocks₂₁, add_sub_cancel_left]
  have hC : u ∈ parabolicCell m n := by
    change (lead u.val).det ≠ 0
    rw [hA]
    exact (determinant a).ne_zero
  rw [compactSection, ite_eq_left hC, sectionFormula, hA, hS, hY, unitsExtension_val, unitsExtension_val]

/-- A smooth product of Levi sections and a compact smooth rectangle kernel gives a genuine
smooth section supported in the open real parabolic cell. -/
def RealParabolicCompactSectionStatement : Prop :=
  ∀ (m n : ℕ) (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (φ : X m n → ℂ), ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f →
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    ContMDiff (matrixModel ℝ (m + n)) 𝓘(ℝ, ℂ) ∞ (compactSection z₁ z₂ f g φ) ∧
    tsupport (compactSection z₁ z₂ f g φ) ⊆ parabolicCell m n ∧
    ∀ (u : G (m + n)) (a : G m) (b : G n) (C : X n m) (Y : X m n),
      split u.val = Matrix.fromBlocks a.val (a.val * Y) C (C * Y + b.val) →
      compactSection z₁ z₂ f g φ u = detWeight z₁ a.val * detWeight z₂ b.val * f a * g b * φ Y

theorem realParabolicCompactSection : RealParabolicCompactSectionStatement := by
  intro m n z₁ z₂ f g φ hf hg hφ hφC
  exact ⟨contMDiff_compactSection z₁ z₂ f g hf hg φ hφ hφC,
    (tsupport_compactSection_subset z₁ z₂ f g φ hφC).trans (rectangleSupport_subset_cell _),
    compactSection_of_split z₁ z₂ f g φ⟩

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
