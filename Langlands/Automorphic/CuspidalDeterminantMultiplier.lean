import Langlands.Automorphic.DeterminantMultiplier
import Langlands.Automorphic.ConstantTerm

/-! # Determinant multiplication and actual cuspidal functions -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

namespace Langlands.GeneralLinear

/-- Every standard upper block-unipotent matrix has determinant one. -/
@[simp]
theorem determinant_blockUnipotent {R : Type*} [CommRing R] {a b n : ℕ}
    (h : a + b = n) (X : Matrix (Fin a) (Fin b) R) :
    determinant (blockUnipotent h X) = 1 := by
  apply Units.ext
  change Matrix.det (blockUnipotent h X : Matrix (Fin n) (Fin n) R) = 1
  simp only [blockUnipotent_val, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

end Langlands.GeneralLinear

namespace Langlands.Global.HeckeCharacter

open Langlands.GeneralLinear

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

@[simp]
theorem adelicDeterminant_blockUnipotent (χ : HeckeCharacter F) {a b : ℕ}
    (h : a + b = n) (X : Matrix (Fin a) (Fin b) (Adeles F)) :
    χ.adelicDeterminant n (blockUnipotent h X) = 1 := by
  change χ.onIdeles (determinant (blockUnipotent h X)) = 1
  rw [determinant_blockUnipotent, map_one]

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ContinuousRationalFunctions MeasureTheory

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance cuspidalMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance cuspidalMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _

/-- The determinant character is constant along the unipotent variable. -/
theorem constantTermIntegrand_determinantMultiplier (χ : HeckeCharacter F)
    {a b : ℕ} (h : a + b = n) (f : ContinuousRationalFunctions F n)
    (g : AdelicGL F n) (X : Matrix (Fin a) (Fin b) (AdeleQuotient F)) :
    constantTermIntegrand F n h (determinantMultiplier n χ f) g X =
      (χ.adelicDeterminant n g : ℂ) * constantTermIntegrand F n h f g X := by
  unfold constantTermIntegrand
  rw [evaluate_determinantMultiplier, map_mul,
    HeckeCharacter.adelicDeterminant_blockUnipotent, one_mul]

variable [CompactSpace (AdeleQuotient F)]

/-- Actual maximal-block constant terms commute with determinant multiplication. -/
theorem constantTerm_determinantMultiplier (χ : HeckeCharacter F)
    {a b : ℕ} (h : a + b = n) (f : ContinuousRationalFunctions F n)
    (g : AdelicGL F n) :
    constantTerm F n h (determinantMultiplier n χ f) g =
      (χ.adelicDeterminant n g : ℂ) * constantTerm F n h f g := by
  unfold constantTerm
  simp_rw [constantTermIntegrand_determinantMultiplier]
  exact integral_const_mul _ _

/-- Multiplication by every actual Hecke character preserves cuspidality. -/
theorem IsCuspidal.determinantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n} (hf : IsCuspidal F n f) :
    IsCuspidal F n (ContinuousRationalFunctions.determinantMultiplier n χ f) := by
  intro a b h ha hb g
  rw [constantTerm_determinantMultiplier, hf a b h ha hb g, mul_zero]

@[simp]
theorem isCuspidal_determinantMultiplier_iff (χ : HeckeCharacter F)
    (f : ContinuousRationalFunctions F n) :
    IsCuspidal F n (determinantMultiplier n χ f) ↔ IsCuspidal F n f := by
  constructor
  · intro hf
    have hi := hf.determinantMultiplier n χ⁻¹
    change IsCuspidal F n (determinantMul n χ⁻¹ (determinantMul n χ f)) at hi
    rw [determinantMul_inv_apply] at hi
    exact hi
  · exact fun hf => hf.determinantMultiplier n χ

/-- The existing actual cuspidal submodule, with its inherited topology. -/
abbrev CuspidalContinuousFunctions :=
  (cuspidalSubrepresentation (K := F) (n := n)).toSubmodule

local instance cuspidalMultiplierGroup :
    AddCommGroup (CuspidalContinuousFunctions (F := F) n) := Submodule.addCommGroup _

namespace CuspidalContinuousFunctions

private theorem determinantMultiplier_map (χ : HeckeCharacter F) :
    (cuspidalSubrepresentation (K := F) (n := n)).toSubmodule.map
      (ContinuousRationalFunctions.determinantMultiplier n χ).toLinearMap =
        (cuspidalSubrepresentation (K := F) (n := n)).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg.determinantMultiplier n χ
  · intro hf
    refine ⟨ContinuousRationalFunctions.determinantMultiplier n χ⁻¹ f,
      hf.determinantMultiplier n χ⁻¹, ?_⟩
    change determinantMul n χ (determinantMul n χ⁻¹ f) = f
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f

/-- Restrict the actual ambient multiplier to its invariant cuspidal submodule. -/
def determinantMultiplier (χ : HeckeCharacter F) :
    CuspidalContinuousFunctions (F := F) n ≃L[ℂ]
      CuspidalContinuousFunctions (F := F) n :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (determinantMultiplier_map n χ)

@[simp]
theorem evaluate_determinantMultiplier (χ : HeckeCharacter F)
    (f : CuspidalContinuousFunctions (F := F) n) (g : AdelicGL F n) :
    evaluate F n (determinantMultiplier n χ f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

@[simp]
theorem evaluate_determinantMultiplier_symm (χ : HeckeCharacter F)
    (f : CuspidalContinuousFunctions (F := F) n) (g : AdelicGL F n) :
    evaluate F n ((determinantMultiplier n χ).symm f).val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val g := rfl

/-- The restricted right action has the same determinant-character covariance. -/
theorem determinantMultiplier_rightAction (χ : HeckeCharacter F)
    (g : AdelicGL F n) (f : CuspidalContinuousFunctions (F := F) n) :
    (cuspidalSubrepresentation (K := F) (n := n)).toRepresentation g
        (determinantMultiplier n χ f) =
      (χ.adelicDeterminant n g : ℂ) • determinantMultiplier n χ
        ((cuspidalSubrepresentation (K := F) (n := n)).toRepresentation g f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ g f.val

end CuspidalContinuousFunctions
end Langlands.Automorphic
