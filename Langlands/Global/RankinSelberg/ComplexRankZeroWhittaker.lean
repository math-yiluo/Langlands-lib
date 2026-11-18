import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Mathlib.Analysis.Normed.Module.Connected

/-! # The Whittaker model of a character of `GL₁(ℂ)`

Every function in the Whittaker model `complexWhittakerModel 0 [c] a` of the complex standard
module of a single character `c` is a constant multiple of `g ↦ χ_c(det g)`. See the paired
Markdown.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexRankZero

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

/-! ### The character `χ_d ∘ det` of `GL₁(ℂ)` -/

section Character

variable (d : ComplexCharacterData)

/-- The function `g ↦ χ_d(det g)` on `GL₁(ℂ)`. -/
def characterFunction : Langlands.GeneralLinear (0 + 1) ℂ → ℂ :=
  fun g => (d.character (GeneralLinear.determinant g) : ℂ)

theorem characterFunction_mul (g h : Langlands.GeneralLinear (0 + 1) ℂ) :
    characterFunction d (g * h) = characterFunction d g * characterFunction d h := by
  simp only [characterFunction, map_mul, Units.val_mul]

theorem characterFunction_one : characterFunction d 1 = 1 := by
  simp only [characterFunction, map_one, Units.val_one]

theorem characterFunction_mul_inv (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    characterFunction d g * characterFunction d.inv g = 1 := by
  simp only [characterFunction, ComplexCharacterData.inv_character_apply]
  exact mul_inv_cancel₀ (Units.ne_zero _)

theorem diagonalUnits_determinant (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    (GeneralLinear.Iwasawa.diagonalUnits (fun _ : Fin (0 + 1) => GeneralLinear.determinant g) :
      Langlands.GeneralLinear (0 + 1) ℂ) = g := by
  apply Units.ext
  rw [GeneralLinear.Iwasawa.diagonalUnits_val]
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  rw [Matrix.diagonal_apply_eq]
  change (g : Matrix (Fin 1) (Fin 1) ℂ).det = _
  exact Matrix.det_fin_one _

theorem principalSeriesCharacter_rankOne (a : Fin (0 + 1) → ℂˣ) :
    principalSeriesCharacter ℂ (0 + 1) (complexPositionCharacter [d]) a =
      (d.character (a 0) : ℂ) := by
  simp [principalSeriesCharacter, complexPositionCharacter]

/-- Every function in the standard module of `[d]` on `GL₁(ℂ)` is `f(1) · χ_d ∘ det`. -/
theorem eq_mul_characterFunction {f : Langlands.GeneralLinear (0 + 1) ℂ → ℂ}
    (hf : f ∈ complexStandardModule (0 + 1) [d]) (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    f g = f 1 * characterFunction d g := by
  have h := hf.2 (fun _ => GeneralLinear.determinant g) 1 1
  rw [OneMemClass.coe_one, mul_one, mul_one, diagonalUnits_determinant,
    principalSeriesCharacter_rankOne] at h
  rw [h, characterFunction, mul_comm]

/-- `χ_d ∘ det` is a `U(1)`-finite vector of the standard module of `[d]`: the module is
nonzero (`complexStandardNontrivial`) and every element is a multiple of `χ_d ∘ det`. -/
theorem characterFunction_mem :
    characterFunction d ∈ Automorphic.complexStandardKFinite (0 + 1) [d] := by
  have := complexStandardNontrivial (0 + 1) [d] rfl
  obtain ⟨f, hf0⟩ := exists_ne
    (0 : kFiniteFunctions (complexStandardModule (0 + 1) [d]) (unitaryCompact ℂ (0 + 1)))
  have hmod : (f : Langlands.GeneralLinear (0 + 1) ℂ → ℂ) ∈ complexStandardModule (0 + 1) [d] :=
    (Submodule.mem_inf.mp f.2).1
  have heq := eq_mul_characterFunction d hmod
  have h1 : (f : Langlands.GeneralLinear (0 + 1) ℂ → ℂ) 1 ≠ 0 := by
    intro h
    apply hf0
    apply Subtype.ext
    funext g
    rw [heq g, h, zero_mul]
    rfl
  have hχ : characterFunction d =
      ((f : Langlands.GeneralLinear (0 + 1) ℂ → ℂ) 1)⁻¹ •
        (f : Langlands.GeneralLinear (0 + 1) ℂ → ℂ) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, heq g, ← mul_assoc, inv_mul_cancel₀ h1, one_mul]
  rw [hχ]
  exact Submodule.smul_mem _ _ f.2

theorem contMDiff_characterFunction :
    ContMDiff (matrixModel ℂ (0 + 1)) 𝓘(ℝ, ℂ) ∞ (characterFunction d) :=
  (Submodule.mem_inf.mp (characterFunction_mem d)).1.1

/-- The right derivative of `χ_d ∘ det` is `χ_d ∘ det` times its value at `1`. -/
theorem rightDerivative_characterFunction (X : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ)
    (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    rightDerivative (matrixModel ℂ (0 + 1)) X (characterFunction d) g =
      characterFunction d g * rightDerivative (matrixModel ℂ (0 + 1)) X (characterFunction d) 1 := by
  have h := rightDerivative_mul_left_of_eq (contMDiff_characterFunction d)
    (a := g) (c := characterFunction d g) (fun h => characterFunction_mul d g h) X 1
  rwa [mul_one] at h

theorem rightDerivative_const (X : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ)
    (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    rightDerivative (matrixModel ℂ (0 + 1)) X (fun _ => (1 : ℂ)) g = 0 := by
  simp only [rightDerivative, mfderiv_const]
  rfl

/-- The right derivatives of `χ_d ∘ det` and `χ_d⁻¹ ∘ det` at `1` are opposite. -/
theorem rightDerivative_add_inv (X : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) :
    rightDerivative (matrixModel ℂ (0 + 1)) X (characterFunction d) 1 +
      rightDerivative (matrixModel ℂ (0 + 1)) X (characterFunction d.inv) 1 = 0 := by
  have h := ComplexTemperedComplement.rightDerivative_mul_fun (contMDiff_characterFunction d)
    (contMDiff_characterFunction d.inv) X 1
  simp only [characterFunction_mul_inv, characterFunction_one, mul_one, one_mul,
    rightDerivative_const] at h
  exact h.symm

end Character

/-! ### Connectedness of `GL₁(ℂ)` in the matrix model -/

theorem isConnected_setOf_isUnit :
    IsConnected {y : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ | IsUnit y} := by
  have hc : IsConnected ({0}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 0
  have himage : (fun z : ℂ => (Matrix.of fun _ _ => z : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ)) ''
      {0}ᶜ = {y | IsUnit y} := by
    ext y
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : y.det = y 0 0 := Matrix.det_fin_one y
    rw [hdet, isUnit_iff_ne_zero]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      refine ⟨y 0 0, hy, ?_⟩
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      rfl
  rw [← himage]
  exact hc.image _ (continuous_pi fun _ => continuous_pi fun _ => continuous_id).continuousOn

/-! ### Whittaker intertwiners -/

section Intertwiner

variable (c : ComplexCharacterData) (a : ℂˣ)

/-- `χ_c ∘ det` as an element of the `U(1)`-finite standard module of `[c]`. -/
def characterVector : Automorphic.complexStandardKFinite (0 + 1) [c] :=
  ⟨characterFunction c, characterFunction_mem c⟩

variable {c a}

/-- A function on `GL₁(ℂ)` that is smooth and satisfies `R(X) F = μ_X F` with
`μ_X = R(X)(χ_c ∘ det)(1)` for every `X` is `F(1) · χ_c ∘ det`. -/
theorem eq_of_rightDerivative {F : Langlands.GeneralLinear (0 + 1) ℂ → ℂ}
    (hF : ContMDiff (matrixModel ℂ (0 + 1)) 𝓘(ℝ, ℂ) ∞ F)
    (hX : ∀ (X : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) (g : Langlands.GeneralLinear (0 + 1) ℂ),
      rightDerivative (matrixModel ℂ (0 + 1)) X F g =
        rightDerivative (matrixModel ℂ (0 + 1)) X (characterFunction c) 1 * F g)
    (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    F g = F 1 * characterFunction c g := by
  set ψ : Langlands.GeneralLinear (0 + 1) ℂ → ℂ := fun g => F g * characterFunction c.inv g
    with hψ_def
  have hψ : ContMDiff (matrixModel ℂ (0 + 1)) 𝓘(ℝ, ℂ) ∞ ψ :=
    ComplexJacquetLimit.contMDiff_mul_fun hF (contMDiff_characterFunction c.inv)
  have hRψ : ∀ (X : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) (g : Langlands.GeneralLinear (0 + 1) ℂ),
      rightDerivative (matrixModel ℂ (0 + 1)) X ψ g = 0 := by
    intro X g
    rw [hψ_def, ComplexTemperedComplement.rightDerivative_mul_fun hF
      (contMDiff_characterFunction c.inv), hX, rightDerivative_characterFunction c.inv,
      eq_neg_of_add_eq_zero_right (rightDerivative_add_inv c X)]
    ring
  set U : Set (Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) := {y | IsUnit y} with hU
  have hdiff : DifferentiableOn ℝ (unitsExtension ψ) U :=
    fun y hy => (differentiableAt_unitsExtension hψ hy).differentiableWithinAt
  have hzero : U.EqOn (fderiv ℝ (unitsExtension ψ)) 0 := by
    intro y hy
    ext v
    set h : Langlands.GeneralLinear (0 + 1) ℂ := IsUnit.unit hy
    have hval : (h : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) = y := IsUnit.unit_spec hy
    have hR := rightDerivative_eq_fderiv hψ
      (((h⁻¹ : Langlands.GeneralLinear (0 + 1) ℂ) : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) * v) h
    rw [hRψ, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, hval] at hR
    rw [← hR]
    rfl
  have hconst := isOpen_setOf_isUnit_matrix.is_const_of_fderiv_eq_zero
    isConnected_setOf_isUnit.isPreconnected hdiff hzero (Units.isUnit g) (Units.isUnit 1)
  rw [unitsExtension_val ψ g, unitsExtension_val ψ 1] at hconst
  have hψg : ψ g = F 1 := by
    rw [hconst, hψ_def]
    simp only [characterFunction_one, mul_one]
  calc F g = F g * (characterFunction c.inv g * characterFunction c g) := by
        rw [mul_comm (characterFunction c.inv g), characterFunction_mul_inv, mul_one]
    _ = ψ g * characterFunction c g := by rw [hψ_def]; ring
    _ = F 1 * characterFunction c g := by rw [hψg]

/-- The value of a Whittaker intertwiner of `[c]` on `χ_c ∘ det` is a multiple of `χ_c ∘ det`. -/
theorem intertwiner_characterVector {B : Automorphic.complexStandardKFinite (0 + 1) [c] →ₗ[ℂ]
      (Langlands.GeneralLinear (0 + 1) ℂ → ℂ)}
    (hB : IsComplexWhittakerIntertwiner 0 [c] a B) (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    B (characterVector c) g = B (characterVector c) 1 * characterFunction c g := by
  refine eq_of_rightDerivative (hB.2.1 (characterVector c)) (fun X h => ?_) g
  set μ := rightDerivative (matrixModel ℂ (0 + 1)) X (characterFunction c) 1
  have hder : ((μ • characterVector c : Automorphic.complexStandardKFinite (0 + 1) [c]) :
      Langlands.GeneralLinear (0 + 1) ℂ → ℂ) =
        rightDerivative (matrixModel ℂ (0 + 1)) X
          ((characterVector c : Automorphic.complexStandardKFinite (0 + 1) [c]) :
            Langlands.GeneralLinear (0 + 1) ℂ → ℂ) := by
    funext k
    change μ * characterFunction c k = _
    change _ = rightDerivative (matrixModel ℂ (0 + 1)) X (characterFunction c) k
    rw [rightDerivative_characterFunction c X k, mul_comm]
  have h1 := hB.2.2.2.2 X (characterVector c) (μ • characterVector c) hder
  rw [← h1, map_smul]
  rfl

/-- **The Whittaker model of a character of `GL₁(ℂ)`.** Every `W` in
`complexWhittakerModel 0 [c] a` is `C · χ_c ∘ det` for some constant `C`. -/
theorem exists_eq_of_mem_complexWhittakerModel {W : Langlands.GeneralLinear (0 + 1) ℂ → ℂ}
    (hW : W ∈ complexWhittakerModel 0 [c] a) :
    ∃ C : ℂ, ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ) := by
  have hle : complexWhittakerModel 0 [c] a ≤ Submodule.span ℂ {characterFunction c} := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    have hmod : (f : Langlands.GeneralLinear (0 + 1) ℂ → ℂ) ∈ complexStandardModule (0 + 1) [c] :=
      (Submodule.mem_inf.mp f.2).1
    have hf : f = (f : Langlands.GeneralLinear (0 + 1) ℂ → ℂ) 1 • characterVector c := by
      apply Subtype.ext
      funext g
      exact eq_mul_characterFunction c hmod g
    rw [hf, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.mem_span_singleton.mpr
      ⟨B (characterVector c) 1, ?_⟩)
    funext g
    rw [intertwiner_characterVector hB g]
    rfl
  obtain ⟨C, hC⟩ := Submodule.mem_span_singleton.mp (hle hW)
  exact ⟨C, fun g => by rw [← hC]; rfl⟩

end Intertwiner

end Langlands.Global.RankinSelbergGlobal.ComplexRankZero
