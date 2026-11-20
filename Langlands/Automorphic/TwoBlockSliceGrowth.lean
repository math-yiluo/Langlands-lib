import Langlands.Automorphic.TwoBlockConstantTermGrowth
import Langlands.Automorphic.TwoBlockConstantTermSlices
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.RingTheory.Finiteness.Prod

/-! # Polynomial growth of the finite-smooth constant-term slices -/

noncomputable section
universe u

open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global ArchimedeanGL ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "A" => AdelicGL F
local notation "G∞" => InfiniteAdelicGL F
local notation "Gf" => FiniteAdelicGL F
local notation "M" => ArchimedeanMatrix F
local notation "κ" => archimedeanGLCoordinates F

local instance blockSliceGrowthRationalGroup (r : ℕ) :
    AddCommGroup (RationalInvariantFunctions F r) := Submodule.addCommGroup _
local instance blockSliceGrowthContinuousGroup (r : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F r) := Submodule.addCommGroup _
local instance blockSliceGrowthFiniteSmoothGroup (r : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F r) := Submodule.addCommGroup _
local instance blockSliceGrowthFormGroup (r : ℕ) :
    AddCommGroup (AutomorphicForms F r) := Submodule.addCommGroup _

private theorem blockDiagonalEmbedding_height_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G∞ a) (y : G∞ b),
      matrixHeight F n (blockDiagonalEmbedding h (x, y)) ≤
        C * (matrixHeight F a x * matrixHeight F b y) := by
  let : FiniteDimensional ℝ (M a × M b) := Module.Finite.prod
  let B : (M a × M b) →L[ℝ] M n := (blockDiagonalMatrixMap F h).toContinuousLinearMap
  let C : ℝ := max 1 ‖B‖
  have hC : 1 ≤ C := le_max_left _ _
  have hval (x : G∞ a) (y : G∞ b) :
      ‖(κ n (blockDiagonalEmbedding h (x, y))).val‖ ≤
        C * (matrixHeight F a x * matrixHeight F b y) := by
    have he : (κ n (blockDiagonalEmbedding h (x, y))).val =
        B ((κ a x).val, (κ b y).val) := by
      change (Matrix.GeneralLinearGroup.map
        (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
        (blockDiagonalEmbedding h (x, y))).val =
          blockDiagonalMatrixMap F h ((κ a x).val, (κ b y).val)
      rw [map_blockDiagonalEmbedding, blockDiagonalMatrixMap_apply]
      rfl
    have hnorm : ‖((κ a x).val, (κ b y).val)‖ ≤ matrixHeight F a x * matrixHeight F b y := by
      rw [Prod.norm_def]
      exact max_le
        ((norm_val_le_matrixHeight F a x).trans
          (le_mul_of_one_le_right (matrixHeight_nonneg F a x) (one_le_matrixHeight F b y)))
        ((norm_val_le_matrixHeight F b y).trans
          (le_mul_of_one_le_left (matrixHeight_nonneg F b y) (one_le_matrixHeight F a x)))
    rw [he]
    exact (B.le_opNorm _).trans
      (mul_le_mul (le_max_right _ _) hnorm (norm_nonneg _) (zero_le_one.trans hC))
  refine ⟨C, zero_le_one.trans hC, fun x y => max_le ?_ (max_le (hval x y) ?_)⟩
  · exact one_le_mul_of_one_le_of_one_le hC
      (one_le_mul_of_one_le_of_one_le (one_le_matrixHeight F a x) (one_le_matrixHeight F b y))
  · have hi := hval x⁻¹ y⁻¹
    rw [matrixHeight_inv, matrixHeight_inv,
      ← show (x, y)⁻¹ = (x⁻¹, y⁻¹) from rfl, map_inv, map_inv] at hi
    exact hi

private theorem polynomialGrowth_of_height_le {r : ℕ} (e : G∞ r → G∞ n)
    (C : ℝ) (hC : 0 ≤ C) (he : ∀ x, matrixHeight F n (e x) ≤ C * matrixHeight F r x)
    (f : G∞ n → ℂ) (hf : ArchimedeanGL.HasPolynomialGrowth F n f) :
    ArchimedeanGL.HasPolynomialGrowth F r (fun x => f (e x)) := by
  obtain ⟨D, hD, k, hk⟩ := hf
  refine ⟨D * C ^ k, mul_nonneg hD (pow_nonneg hC _), k, fun x => (hk _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (matrixHeight_nonneg F n _) (he x) _) hD

variable [CompactSpace (AdeleQuotient F)]

private theorem automorphicConstantTerm_hasPolynomialGrowth (L : OpenSubgroup (Gf n))
    (f : AutomorphicForms F n) (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f)
    (d : Gf n) : ArchimedeanGL.HasPolynomialGrowth F n
      (fun g => constantTerm F n h f.val.val (AdelicGL.pair F n g d)) := by
  apply constantTerm_hasPolynomialGrowth F h _ L
  · intro l
    change finiteRightAction F n l.val
      (automorphicToContinuous F n f) = automorphicToContinuous F n f
    rw [← automorphicToContinuous_finiteRightAction, hf]
  · exact ((mem_automorphicSubrepresentation F n f.val).mp f.property).2.2.2

/-- At every fixed finite argument, the first slice has polynomial growth in its own rank. -/
theorem firstBlockConstantTerm_hasPolynomialGrowth (d : Gf n) (y : A b)
    (f : AutomorphicForms F n) (L : OpenSubgroup (Gf n))
    (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) :
    HasPolynomialGrowth F a (firstBlockConstantTermContinuous F h d y f) := by
  intro l
  let yInf := AdelicGL.infinite F b y
  let d' := blockDiagonalEmbedding h (l, AdelicGL.finite F b y) * d
  obtain ⟨C, hC, hB⟩ := blockDiagonalEmbedding_height_bound F h
  have hg := polynomialGrowth_of_height_le F (fun x => blockDiagonalEmbedding h (x, yInf))
    (C * matrixHeight F b yInf) (mul_nonneg hC (matrixHeight_nonneg F b yInf))
    (fun x => by
      simpa only [mul_assoc, mul_comm (matrixHeight F b yInf) (matrixHeight F a x)] using hB x yInf)
    _ (automorphicConstantTerm_hasPolynomialGrowth F h L f hf d')
  have he : infiniteSlice F a l (firstBlockConstantTermContinuous F h d y f) =
      fun x => constantTerm F n h f.val.val
        (AdelicGL.pair F n (blockDiagonalEmbedding h (x, yInf)) d') := by
    funext x
    change blockConstantTermAt F n h d f (AdelicGL.pair F a x l, y) = _
    change constantTerm F n h f.val.val
      (blockDiagonalEmbedding h (AdelicGL.pair F a x l, y) * AdelicGL.ofFinite F n d) = _
    rw [blockDiagonalEmbedding_mul_ofFinite_eq_pair, AdelicGL.infinite_pair, AdelicGL.finite_pair]
  simpa only [he] using hg

/-- At every fixed finite argument, the second slice has polynomial growth in its own rank. -/
theorem secondBlockConstantTerm_hasPolynomialGrowth (d : Gf n) (x : A a)
    (f : AutomorphicForms F n) (L : OpenSubgroup (Gf n))
    (hf : ∀ l : L, automorphicFiniteRightAction F n l.val f = f) :
    HasPolynomialGrowth F b (secondBlockConstantTermContinuous F h d x f) := by
  intro l
  let xInf := AdelicGL.infinite F a x
  let d' := blockDiagonalEmbedding h (AdelicGL.finite F a x, l) * d
  obtain ⟨C, hC, hB⟩ := blockDiagonalEmbedding_height_bound F h
  have hg := polynomialGrowth_of_height_le F (fun y => blockDiagonalEmbedding h (xInf, y))
    (C * matrixHeight F a xInf) (mul_nonneg hC (matrixHeight_nonneg F a xInf))
    (fun y => by simpa only [mul_assoc] using hB xInf y)
    _ (automorphicConstantTerm_hasPolynomialGrowth F h L f hf d')
  have he : infiniteSlice F b l (secondBlockConstantTermContinuous F h d x f) =
      fun y => constantTerm F n h f.val.val
        (AdelicGL.pair F n (blockDiagonalEmbedding h (xInf, y)) d') := by
    funext y
    change blockConstantTermAt F n h d f (x, AdelicGL.pair F b y l) = _
    change constantTerm F n h f.val.val
      (blockDiagonalEmbedding h (x, AdelicGL.pair F b y l) * AdelicGL.ofFinite F n d) = _
    rw [blockDiagonalEmbedding_mul_ofFinite_eq_pair, AdelicGL.infinite_pair, AdelicGL.finite_pair]
  simpa only [he] using hg

end Langlands.Automorphic
