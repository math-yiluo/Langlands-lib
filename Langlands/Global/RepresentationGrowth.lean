import Langlands.GroupScheme.MatrixRepresentation
import Langlands.Global.AdelicGroupPointTopology
import Langlands.Global.ArchimedeanGrowth
import Mathlib.RepresentationTheory.Basic

/-! # Polynomial growth relative to an actual algebraic matrix representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

namespace Langlands.Global.RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {N : ℕ}
  (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- The specified algebraic representation evaluated on actual infinite adelic points. -/
def infiniteMatrix : InfiniteAdelicGroupPoints F G →ₜ* InfiniteAdelicGL F N where
  toMonoidHom := (GeneralLinearGroupPoints.infiniteHomeomorph F N).toMonoidHom.comp
    (G.affinePointsTarget rho (CommAlgCat.of F (InfiniteAdeleRing F)))
  continuous_toFun := (GeneralLinearGroupPoints.infiniteHomeomorph F N).continuous.comp
    (G.continuous_affinePointsTarget (CommAlgCat.of F (InfiniteAdeleRing F)) rho)

/-- Pull back the original matrix-and-inverse height through the actual representation. -/
def height (g : InfiniteAdelicGroupPoints F G) : ℝ :=
  ArchimedeanGL.matrixHeight F N (infiniteMatrix F G rho g)

theorem one_le_height (g : InfiniteAdelicGroupPoints F G) : 1 ≤ height F G rho g :=
  ArchimedeanGL.one_le_matrixHeight F N _

theorem height_nonneg (g : InfiniteAdelicGroupPoints F G) : 0 ≤ height F G rho g :=
  le_trans zero_le_one (one_le_height F G rho g)

theorem continuous_height : Continuous (height F G rho) :=
  (ArchimedeanGL.continuous_matrixHeight F N).comp (infiniteMatrix F G rho).continuous

@[simp] theorem height_inv (g : InfiniteAdelicGroupPoints F G) :
    height F G rho g⁻¹ = height F G rho g := by
  simp only [height, map_inv, ArchimedeanGL.matrixHeight_inv]

theorem height_mul_le (g h : InfiniteAdelicGroupPoints F G) :
    height F G rho (g * h) ≤ height F G rho g * height F G rho h := by
  simpa only [height, map_mul] using
    ArchimedeanGL.matrixHeight_mul_le F N (infiniteMatrix F G rho g)
      (infiniteMatrix F G rho h)

/-- A polynomial bound for the height of the specified representation; no regularity is imposed. -/
def HasPolynomialGrowth (f : InfiniteAdelicGroupPoints F G → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ g, ‖f g‖ ≤ C * height F G rho g ^ d

variable {F G rho}

theorem HasPolynomialGrowth.zero :
    HasPolynomialGrowth F G rho (0 : InfiniteAdelicGroupPoints F G → ℂ) :=
  ⟨0, le_refl 0, 0, by simp⟩

theorem HasPolynomialGrowth.const (c : ℂ) :
    HasPolynomialGrowth F G rho (fun _ : InfiniteAdelicGroupPoints F G => c) :=
  ⟨‖c‖, norm_nonneg _, 0, by simp⟩

theorem HasPolynomialGrowth.add {f h : InfiniteAdelicGroupPoints F G → ℂ}
    (hf : HasPolynomialGrowth F G rho f) (hh : HasPolynomialGrowth F G rho h) :
    HasPolynomialGrowth F G rho (f + h) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  obtain ⟨D, hD, e, hh⟩ := hh
  refine ⟨C + D, add_nonneg hC hD, max d e, ?_⟩
  intro g
  calc
    ‖(f + h) g‖ ≤ ‖f g‖ + ‖h g‖ := norm_add_le _ _
    _ ≤ C * height F G rho g ^ d + D * height F G rho g ^ e := add_le_add (hf g) (hh g)
    _ ≤ C * height F G rho g ^ max d e + D * height F G rho g ^ max d e :=
      add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (one_le_height F G rho g) (le_max_left d e)) hC)
        (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (one_le_height F G rho g) (le_max_right d e)) hD)
    _ = (C + D) * height F G rho g ^ max d e := (add_mul _ _ _).symm

theorem HasPolynomialGrowth.smul {f : InfiniteAdelicGroupPoints F G → ℂ}
    (hf : HasPolynomialGrowth F G rho f) (c : ℂ) :
    HasPolynomialGrowth F G rho (c • f) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, d, ?_⟩
  intro g
  calc
    ‖(c • f) g‖ = ‖c‖ * ‖f g‖ := norm_mul _ _
    _ ≤ ‖c‖ * (C * height F G rho g ^ d) :=
      mul_le_mul_of_nonneg_left (hf g) (norm_nonneg _)
    _ = (‖c‖ * C) * height F G rho g ^ d := (mul_assoc _ _ _).symm

theorem HasPolynomialGrowth.rightTranslate {f : InfiniteAdelicGroupPoints F G → ℂ}
    (hf : HasPolynomialGrowth F G rho f) (h : InfiniteAdelicGroupPoints F G) :
    HasPolynomialGrowth F G rho (fun g => f (g * h)) := by
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨C * height F G rho h ^ d,
    mul_nonneg hC (pow_nonneg (height_nonneg F G rho h) d), d, ?_⟩
  intro g
  calc
    ‖f (g * h)‖ ≤ C * height F G rho (g * h) ^ d := hf _
    _ ≤ C * (height F G rho g * height F G rho h) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (height_nonneg F G rho _) (height_mul_le F G rho g h) d) hC
    _ = (C * height F G rho h ^ d) * height F G rho g ^ d := by rw [mul_pow]; ring

theorem hasPolynomialGrowth_rightTranslate_iff (f : InfiniteAdelicGroupPoints F G → ℂ)
    (h : InfiniteAdelicGroupPoints F G) :
    HasPolynomialGrowth F G rho (fun g => f (g * h)) ↔ HasPolynomialGrowth F G rho f := by
  constructor
  · intro hf
    simpa only [inv_mul_cancel_right] using hf.rightTranslate h⁻¹
  · exact fun hf => hf.rightTranslate h

variable (F G rho)

/-- The actual complex function submodule defined by this representation's polynomial bounds. -/
def polynomialGrowthFunctions : Submodule ℂ (InfiniteAdelicGroupPoints F G → ℂ) where
  carrier := {f | HasPolynomialGrowth F G rho f}
  zero_mem' := HasPolynomialGrowth.zero
  add_mem' := HasPolynomialGrowth.add
  smul_mem' c _ hf := hf.smul c

@[simp] theorem mem_polynomialGrowthFunctions (f : InfiniteAdelicGroupPoints F G → ℂ) :
    f ∈ polynomialGrowthFunctions F G rho ↔ HasPolynomialGrowth F G rho f := Iff.rfl

/-- Positive right translation restricts to the specified-representation growth space. -/
def polynomialGrowthRightAction :
    Representation ℂ (InfiniteAdelicGroupPoints F G) ↥(polynomialGrowthFunctions F G rho) where
  toFun g :=
    { toFun f := ⟨fun x => f.val (x * g), f.property.rightTranslate g⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    ext f x
    exact congrArg f.val (mul_assoc x g h).symm

@[simp] theorem polynomialGrowthRightAction_apply (g x : InfiniteAdelicGroupPoints F G)
    (f : ↥(polynomialGrowthFunctions F G rho)) :
    (polynomialGrowthRightAction F G rho g f).val x = f.val (x * g) := rfl

section GeneralLinearComparison

variable (n : ℕ)

local notation "GLG" =>
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
local notation "std" => (GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F))

omit [NumberField F] in
/-- The standard representation gives exactly the original infinite matrix point map. -/
@[simp] theorem infiniteMatrix_standard (g : InfiniteAdelicGroupPoints F GLG) :
    infiniteMatrix F GLG std g = GeneralLinearGroupPoints.infiniteHomeomorph F n g := by
  change GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (InfiniteAdeleRing F)) (g ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

/-- The standard height is exactly the original matrix height, with no norm replacement. -/
@[simp] theorem height_standard (g : InfiniteAdelicGroupPoints F GLG) :
    height F GLG std g = ArchimedeanGL.matrixHeight F n
      (GeneralLinearGroupPoints.infiniteHomeomorph F n g) := by
  simp only [height, infiniteMatrix_standard]

/-- The standard growth predicate is equivalent to the original one under the point map. -/
theorem hasPolynomialGrowth_standard_iff (f : InfiniteAdelicGroupPoints F GLG → ℂ) :
    HasPolynomialGrowth F GLG std f ↔
      ArchimedeanGL.HasPolynomialGrowth F n
        (fun g => f ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm g)) := by
  constructor
  · rintro ⟨C, hC, d, hf⟩
    refine ⟨C, hC, d, fun g => ?_⟩
    simpa only [height_standard, ContinuousMulEquiv.apply_symm_apply] using
      hf ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm g)
  · rintro ⟨C, hC, d, hf⟩
    refine ⟨C, hC, d, fun g => ?_⟩
    simpa only [height_standard, ContinuousMulEquiv.symm_apply_apply] using
      hf (GeneralLinearGroupPoints.infiniteHomeomorph F n g)

/-- A genuine complex linear equivalence with the unchanged original polynomial-growth module. -/
def standardPolynomialGrowthEquiv :
    ↥(polynomialGrowthFunctions F GLG std) ≃ₗ[ℂ] ↥(ArchimedeanGL.polynomialGrowthFunctions F n) where
  toFun f := ⟨fun g => f.val ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm g),
    (hasPolynomialGrowth_standard_iff F n f.val).mp f.property⟩
  invFun f := ⟨fun g => f.val (GeneralLinearGroupPoints.infiniteHomeomorph F n g), by
    apply (hasPolynomialGrowth_standard_iff F n _).mpr
    have hf : ArchimedeanGL.HasPolynomialGrowth F n f.val := f.property
    simpa only [ContinuousMulEquiv.apply_symm_apply] using hf⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    exact congrArg f.val ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm_apply_apply g)
  right_inv f := by
    apply Subtype.ext
    funext g
    exact congrArg f.val ((GeneralLinearGroupPoints.infiniteHomeomorph F n).apply_symm_apply g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem standardPolynomialGrowthEquiv_apply
    (f : ↥(polynomialGrowthFunctions F GLG std)) (g : InfiniteAdelicGL F n) :
    (standardPolynomialGrowthEquiv F n f).val g =
      f.val ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm g) := rfl

/-- Under the original matrix realization, the action remains positive right translation. -/
theorem standardPolynomialGrowthEquiv_rightAction
    (h : InfiniteAdelicGroupPoints F GLG)
    (f : ↥(polynomialGrowthFunctions F GLG std)) (g : InfiniteAdelicGL F n) :
    (standardPolynomialGrowthEquiv F n (polynomialGrowthRightAction F GLG std h f)).val g =
      (standardPolynomialGrowthEquiv F n f).val
        (g * GeneralLinearGroupPoints.infiniteHomeomorph F n h) := by
  change f.val ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm g * h) =
    f.val ((GeneralLinearGroupPoints.infiniteHomeomorph F n).symm
      (g * GeneralLinearGroupPoints.infiniteHomeomorph F n h))
  rw [map_mul, ContinuousMulEquiv.symm_apply_apply]

end GeneralLinearComparison

end Langlands.Global.RepresentationGrowth
