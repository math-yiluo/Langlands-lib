import Langlands.Global.RankinSelberg.ComplexGodementCompletionEquivariance
import Langlands.Global.RankinSelberg.ComplexGodementUnitaryCutoff
import Langlands.Global.RankinSelberg.ComplexGodementCompact

/-! # The cofactor lift to compact Godement tests -/

noncomputable section

open Filter Matrix Set
open scoped ContDiff Manifold SchwartzMap Matrix.Norms.Operator Topology

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC normSqC_det_unitary)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
local notation "I" => Fin (n + 1)
local notation "K" => unitaryCompact ℂ (n + 1)
local notation "G" => Langlands.GeneralLinear (n + 1) ℂ
local notation "Rect" => Matrix (Fin n) I ℂ
local notation "Square" => Matrix I I ℂ

/-- Evaluate the square-matrix extension of a larger vector at the cofactor completion,
then multiply by the fixed cutoff. -/
def cofactorTest (χ : Rect → ℂ) : (G → ℂ) →ₗ[ℂ] (Rect → ℂ) where
  toFun f X := χ X * unitsExtension f (specialCompletion X)
  map_add' f g := by
    funext X
    simp only [unitsExtension_add, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext X
    simp only [RingHom.id_apply, unitsExtension_smul, Pi.smul_apply, smul_eq_mul]
    ring

private theorem contDiff_rect_entry (i : Fin n) (j : I) : ContDiff ℝ ∞ (fun X : Rect => X i j) :=
  (Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.contDiff

private theorem contDiff_specialCompletion : ContDiff ℝ ∞ (specialCompletion (n := n)) := by
  have hEntry (i j : I) : ContDiff ℝ ∞ (fun X : Rect => specialCompletion X i j) := by
    refine Fin.cases ?_ (fun r => ?_) i
    · change ContDiff ℝ ∞ (fun X : Rect => (-1 : ℂ) ^ (j : ℕ) *
        ((X.map (starRingEnd ℂ)).submatrix id j.succAbove).det)
      apply contDiff_const.mul
      simp only [Matrix.det_apply']
      exact ContDiff.sum fun p _ => contDiff_const.mul (contDiff_prod fun r _ =>
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_rect_entry (p r) (j.succAbove r)))
    · exact contDiff_rect_entry r j
  rw [show specialCompletion (n := n) = fun X => ∑ i : I, ∑ j : I,
      Matrix.single i j (specialCompletion X i j) from
      funext fun X => Matrix.matrix_eq_sum_single (specialCompletion X)]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    ((Matrix.singleLinearMap ℝ i j : ℂ →ₗ[ℝ] Square).toContinuousLinearMap.contDiff.comp (hEntry i j))

private theorem completion_fullRowRank {X : Rect} (h : IsUnit (specialCompletion X)) :
    HasFullRowRank X := by
  obtain ⟨g, hg⟩ := h
  have hx : X = g.val.submatrix Fin.succ id := by
    rw [hg]
    exact (trailingRows_specialCompletion X).symm
  refine ⟨g⁻¹.val.submatrix id Fin.succ, ?_⟩
  rw [hx, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

private theorem cofactorTest_tsupport_subset (χ : Rect → ℂ) (f : G → ℂ) :
    tsupport (cofactorTest χ f) ⊆ tsupport χ := tsupport_mul_subset_left

private theorem contDiff_cofactorTest (χ : 𝓢(Rect, ℂ)) (f : G → ℂ)
    (hf : ContMDiff (matrixModel ℂ (n + 1)) 𝓘(ℝ, ℂ) ∞ f)
    (hχ : ∀ X ∈ tsupport χ, IsUnit (specialCompletion X)) :
    ContDiff ℝ ∞ (cofactorTest χ f) := by
  rw [contDiff_iff_contDiffAt]
  intro X
  by_cases hX : X ∈ tsupport χ
  · have huCD : ContDiffAt ℝ ∞ (fun Y => unitsExtension f (specialCompletion Y)) X :=
      (contDiffOn_unitsExtension hf).contDiffAt
        (isOpen_setOf_isUnit_matrix.mem_nhds (hχ X hX)) |>.comp X contDiff_specialCompletion.contDiffAt
    exact (χ.smooth ⊤).contDiffAt.mul huCD
  · have he : (fun Y => χ Y) =ᶠ[𝓝 X] 0 := (notMem_tsupport_iff_eventuallyEq.mp hX)
    have he' : cofactorTest χ f =ᶠ[𝓝 X] 0 := he.mono fun Y hY => by
      change χ Y * unitsExtension f (specialCompletion Y) = 0
      rw [show χ Y = 0 from hY, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he'

private theorem norm_det_inverse (k : K) : ‖(↑((determinant k.val)⁻¹) : ℂ)‖ = 1 := by
  have hs := normSqC_det_unitary k
  change ((‖(determinant k.val : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 at hs
  have hsq : ‖(determinant k.val : ℂ)‖ ^ 2 = (1 : ℝ) := by exact_mod_cast hs
  have he := (sq_eq_sq₀ (norm_nonneg (determinant k.val : ℂ)) zero_le_one).mp
    (by simpa only [one_pow] using hsq)
  rw [Units.val_inv_eq_inv_val, norm_inv, he, inv_one]

private theorem leadingPhase_covariance_unit (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) (k : K) (g : G) :
    f (diagonalUnits (Fin.cons (determinant k.val)⁻¹ 1) * g) =
      ((d.character (determinant k.val) : ℂ)⁻¹) * f g := by
  let a : I → ℂˣ := Fin.cons (determinant k.val)⁻¹ 1
  have h := hf.2 a (1 : upperUnipotent (n + 1) ℂ) g
  simp only [Subgroup.coe_one, mul_one] at h
  rw [principalSeriesCharacter, Fin.prod_univ_succ] at h
  simp only [a, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, complexPositionCharacter,
    Pi.one_apply, Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow,
    ComplexSwapJacquet.complexPositionCharacter_one, mul_one, Finset.prod_const_one] at h
  rw [norm_det_inverse k, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  simpa only [map_inv, Units.val_inv_eq_inv_val] using h

theorem cofactorTest_right_mul (χ : Rect → ℂ)
    (hinv : ∀ (X : Rect) (k : K), χ (X * k.val.val) = χ X)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (f : G → ℂ)
    (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) (X : Rect) (k : K) :
    cofactorTest χ (Whittaker.rightTranslation ℂ G k.val f) X =
      (d.character (determinant k.val) : ℂ) * cofactorTest χ f (X * k.val.val) := by
  change χ X * unitsExtension (fun g => f (g * k.val)) (specialCompletion X) =
    (d.character (determinant k.val) : ℂ) * (χ (X * k.val.val) * unitsExtension f (specialCompletion (X * k.val.val)))
  rw [hinv]
  by_cases hX : IsUnit (specialCompletion X)
  · obtain ⟨g, hg⟩ := hX
    let a : I → ℂˣ := Fin.cons (determinant k.val)⁻¹ 1
    have hs : star k.val.val.det = ((determinant k.val)⁻¹ : ℂ) := by
      change star k.val.val.det = k.val.val.det⁻¹
      exact eq_inv_of_mul_eq_one_left (Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary k.2))
    have ha : (diagonalUnits a).val = Matrix.diagonal (Fin.cons (star k.val.val.det) 1) := by
      rw [diagonalUnits_val]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [a, hs]
    have heq : specialCompletion (X * k.val.val) = (diagonalUnits a * (g * k.val)).val := by
      rw [specialCompletion_mul_unitary, ← hg, Units.val_mul, ha, Units.val_mul]
    rw [← hg, heq, unitsExtension_val, unitsExtension_val, leadingPhase_covariance_unit d ds hf k (g * k.val)]
    have hν : (d.character (determinant k.val) : ℂ) ≠ 0 := (d.character (determinant k.val)).ne_zero
    field_simp
  · have hY : ¬ IsUnit (specialCompletion (X * k.val.val)) := by
      simpa only [Matrix.isUnit_iff_isUnit_det, specialCompletion_det_mul_unitary] using hX
    simp only [unitsExtension_of_not_isUnit _ hX, unitsExtension_of_not_isUnit _ hY, mul_zero]

private theorem specialCompletion_trailingRows_one :
    specialCompletion (trailingRows (1 : Square)) = 1 := by
  let A := specialCompletion (trailingRows (1 : Square))
  have hA : A ∈ Matrix.specialUnitaryGroup I ℂ := specialCompletion_mem_specialUnitaryGroup (1 : K)
  obtain ⟨hunit, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
  have hu : A * Aᴴ = 1 := Unitary.mul_star_self_of_mem hunit
  have htop (j : Fin n) : A 0 j.succ = 0 := by
    have h : (A * Aᴴ) 0 j.succ = (1 : Square) 0 j.succ := congrArg (fun M : Square => M 0 j.succ) hu
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, A, trailingRows, Matrix.submatrix_apply,
      Matrix.one_apply, (Fin.succ_ne_zero j).symm, eq_comm] using h
  have hdiag : A = Matrix.diagonal (Fin.cons (A 0 0) 1) := by
    ext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · refine Fin.cases ?_ (fun r => ?_) j
      · simp
      · rw [htop, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero _).symm]
    · simp [A, trailingRows, Matrix.submatrix_apply, Matrix.one_apply, Matrix.diagonal_apply]
  have h00 : A 0 0 = 1 := by
    rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_succ] at hdet
    simpa using hdet
  change A = 1
  rw [hdiag, h00, ← Matrix.diagonal_one]
  congr 1
  funext i
  refine Fin.cases ?_ (fun r => ?_) i <;> simp

/-- The test restricts to the larger compact vector with the distinguished determinant twist removed. -/
theorem cofactorTest_unitaryTrailingRows (χ : Rect → ℂ)
    (hinv : ∀ (X : Rect) (k : K), χ (X * k.val.val) = χ X)
    (hOne : ∀ X ∈ unitaryTrailingRows n, χ X = 1)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (f : G → ℂ)
    (hf : f ∈ complexStandardModule (n + 1) (d :: ds)) (k : K) :
    cofactorTest χ f (trailingRows k.val.val) = (d.character (determinant k.val) : ℂ)⁻¹ * f k.val := by
  let E := trailingRows (1 : Square)
  have hE : χ E = 1 := hOne _ ⟨1, rfl⟩
  have hK : E * k.val.val = trailingRows k.val.val := by
    calc
      _ = ((1 : Square) * k.val.val).submatrix Fin.succ id :=
        (Matrix.submatrix_mul (1 : Square) k.val.val Fin.succ id id Function.bijective_id).symm
      _ = _ := by rw [Matrix.one_mul]; rfl
  have hC : specialCompletion E = (1 : G).val := specialCompletion_trailingRows_one
  have hEval := cofactorTest_right_mul χ hinv d ds f hf E k
  rw [hK] at hEval
  change χ E * unitsExtension (fun g => f (g * k.val)) (specialCompletion E) = _ at hEval
  rw [hE, hC, unitsExtension_val, one_mul, one_mul] at hEval
  rw [hEval, ← mul_assoc, inv_mul_cancel₀ (d.character (determinant k.val)).ne_zero, one_mul]

/-- Compact finiteness passes to the right translates of the cofactor lift. -/
theorem finiteDimensional_cofactorTest_rightOrbit (χ : Rect → ℂ)
    (hinv : ∀ (X : Rect) (k : K), χ (X * k.val.val) = χ X)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (f : G → ℂ)
    (hf : f ∈ complexStandardModule (n + 1) (d :: ds))
    (hFin : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) K) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun X : Rect => cofactorTest χ f (X * k.val.val))) := by
  rw [mem_kFiniteVectors_iff] at hFin
  let V := Submodule.span ℂ (Set.range fun k : K => Whittaker.rightTranslation ℂ G k.val f)
  let : FiniteDimensional ℂ V := hFin
  apply Submodule.finiteDimensional_of_le (S₂ := V.map (cofactorTest χ))
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  let c : ℂ := d.character (determinant k.val)
  have hc : c ≠ 0 := (d.character (determinant k.val)).ne_zero
  refine ⟨c⁻¹ • Whittaker.rightTranslation ℂ G k.val f,
    V.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩), ?_⟩
  rw [map_smul]
  funext X
  change c⁻¹ * cofactorTest χ (Whittaker.rightTranslation ℂ G k.val f) X = _
  rw [cofactorTest_right_mul χ hinv d ds f hf X k]
  change c⁻¹ * (c * cofactorTest χ f (X * k.val.val)) = _
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Choose an invariant cutoff in any invariant neighborhood of the unitary trailing rows,
with invertible cofactor completions throughout its support. -/
theorem exists_cofactorTestCutoff (U : Set Rect) (hU : IsOpen U)
    (hsub : unitaryTrailingRows n ⊆ U) (hinv : ∀ X ∈ U, ∀ k : K, X * k.val.val ∈ U) :
    ∃ χ : 𝓢(Rect, ℂ), HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ X ∈ tsupport χ, IsUnit (specialCompletion X)) ∧
      (∀ X ∈ unitaryTrailingRows n, χ X = 1) ∧
      (∀ (X : Rect) (k : K), χ (X * k.val.val) = χ X) ∧
      ∀ X, ∃ r ∈ Icc (0 : ℝ) 1, χ X = (r : ℂ) := by
  let E := {X : Rect | IsUnit (specialCompletion X)}
  have hE : IsOpen E := isOpen_setOf_isUnit_matrix.preimage contDiff_specialCompletion.continuous
  have hS : unitaryTrailingRows n ⊆ E := by
    rintro _ ⟨k, rfl⟩
    have hk := (Matrix.mem_specialUnitaryGroup_iff.mp (specialCompletion_mem_specialUnitaryGroup k)).2
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (hk ▸ isUnit_one)
  have hStep (X : Rect) (hX : X ∈ U ∩ E) (k : K) : X * k.val.val ∈ U ∩ E := by
    refine ⟨hinv X hX.1 k, ?_⟩
    change IsUnit (specialCompletion (X * k.val.val))
    rw [Matrix.isUnit_iff_isUnit_det, specialCompletion_det_mul_unitary, ← Matrix.isUnit_iff_isUnit_det]
    exact hX.2
  obtain ⟨χ, hχc, hχ, h1, hχinv, hχrange⟩ :=
    complexGodementUnitaryCutoff (U ∩ E) (hU.inter hE) (subset_inter hsub hS) hStep
  exact ⟨χ, hχc, fun _ hX => (hχ hX).1, fun _ hX => (hχ hX).2, h1, hχinv, hχrange⟩

/-- The cofactor lift of a larger standard vector by a compact invariant cutoff is a smooth
full-row-rank Godement test that intertwines right unitary translation with the determinant twist. -/
def ComplexGodementCofactorTestStatement : Prop :=
  ∀ (χ : 𝓢(Rect, ℂ)), HasCompactSupport χ →
    (∀ X ∈ tsupport χ, IsUnit (specialCompletion X)) → (∀ (X : Rect) (k : K), χ (X * k.val.val) = χ X) →
    ∀ (d : ComplexCharacterData) (ds : List ComplexCharacterData) (f : G → ℂ),
      f ∈ complexStandardModule (n + 1) (d :: ds) →
      ∃ Φ : 𝓢(Rect, ℂ), (Φ : Rect → ℂ) = cofactorTest χ f ∧
        HasCompactSupport Φ ∧ (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
        ∀ (X : Rect) (k : K), cofactorTest χ (Whittaker.rightTranslation ℂ G k.val f) X =
          (d.character (determinant k.val) : ℂ) * Φ (X * k.val.val)

theorem complexGodementCofactorTest : ComplexGodementCofactorTestStatement (n := n) := by
  intro χ hχc hχ hinv d ds f hf
  have hsub := cofactorTest_tsupport_subset (χ : Rect → ℂ) f
  have hc : HasCompactSupport (cofactorTest χ f) :=
    hχc.of_isClosed_subset (isClosed_tsupport _) hsub
  refine ⟨hc.toSchwartzMap (contDiff_cofactorTest χ f hf.1 hχ), rfl, hc, ?_, ?_⟩
  · intro X hX
    exact completion_fullRowRank (hχ X (hsub hX))
  · exact cofactorTest_right_mul χ hinv d ds f hf

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
