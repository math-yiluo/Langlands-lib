import Langlands.Automorphic.DeterminantMultiplier
import Langlands.Automorphic.FiniteVectors
import Langlands.Automorphic.Growth
import Langlands.Global.HeckeCharacterFiniteOrder

/-! # Determinant multiplication on subgroup-finite and polynomial-growth functions -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

variable {F : Type u} [Field F] [NumberField F]

/-- A finite-order Hecke character takes values of complex norm one. -/
theorem HasFiniteOrder.norm_apply {χ : HeckeCharacter F} (hχ : χ.HasFiniteOrder)
    (x : IdeleClasses F) : ‖(χ x : ℂ)‖ = 1 := by
  obtain ⟨m, hm, hp⟩ := hχ
  have hx : χ x ^ m = 1 := by
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun,
      Pi.one_apply] using congrArg (fun η : HeckeCharacter F => η x) hp
  apply Complex.norm_eq_one_of_pow_eq_one (n := m) _ hm.ne'
  simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
    congrArg (fun z : ℂˣ => (z : ℂ)) hx

theorem HasFiniteOrder.norm_adelicDeterminant {χ : HeckeCharacter F}
    (hχ : χ.HasFiniteOrder) (n : ℕ) (g : AdelicGL F n) :
    ‖(χ.adelicDeterminant n g : ℂ)‖ = 1 :=
  hχ.norm_apply (ideleClassMap F (AdelicGL.determinant F n g))

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance finiteGrowthMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance finiteGrowthMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteGrowthMultiplierPolynomialGroup :
    AddCommGroup (PolynomialGrowthRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteGrowthMultiplierInfiniteFiniteGroup
    (U : Subgroup (InfiniteAdelicGL F n)) :
    AddCommGroup (InfiniteFiniteRationalFunctions F n U) := Submodule.addCommGroup _

/-- The actual subgroup orbit span is exactly the image of the original orbit span.
No finite-order or compactness hypothesis is needed. -/
theorem infiniteOrbitSpan_determinantMultiplier
    (U : Subgroup (InfiniteAdelicGL F n)) (χ : HeckeCharacter F)
    (f : ContinuousRationalFunctions F n) :
    infiniteOrbitSpan F n U (determinantMultiplier n χ f) =
      (infiniteOrbitSpan F n U f).map (determinantMultiplier n χ).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change continuousRightAction F n (AdelicGL.ofInfinite F n k.val)
      (determinantMultiplier n χ f) ∈ _
    rw [determinantMultiplier_rightAction]
    apply Submodule.smul_mem
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change determinantMultiplier n χ
        (continuousRightAction F n (AdelicGL.ofInfinite F n k.val) f) ∈
      infiniteOrbitSpan F n U (determinantMultiplier n χ f)
    have hk : continuousRightAction F n (AdelicGL.ofInfinite F n k.val)
        (determinantMultiplier n χ f) ∈
        infiniteOrbitSpan F n U (determinantMultiplier n χ f) :=
      Submodule.subset_span ⟨k, rfl⟩
    have hm := (infiniteOrbitSpan F n U (determinantMultiplier n χ f)).smul_mem
      ((χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ)⁻¹) hk
    rw [determinantMultiplier_rightAction, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hm
    exact hm

theorem isInfiniteFinite_determinantMultiplier
    (U : Subgroup (InfiniteAdelicGL F n)) (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n} (hf : IsInfiniteFinite F n U f) :
    IsInfiniteFinite F n U (determinantMultiplier n χ f) := by
  have : Module.Finite ℂ (infiniteOrbitSpan F n U f) := hf
  change Module.Finite ℂ (infiniteOrbitSpan F n U (determinantMultiplier n χ f))
  rw [infiniteOrbitSpan_determinantMultiplier]
  infer_instance

theorem isInfiniteFinite_determinantMultiplier_iff
    (U : Subgroup (InfiniteAdelicGL F n)) (χ : HeckeCharacter F)
    (f : ContinuousRationalFunctions F n) :
    IsInfiniteFinite F n U (determinantMultiplier n χ f) ↔ IsInfiniteFinite F n U f := by
  constructor
  · intro hf
    have hi := isInfiniteFinite_determinantMultiplier n U χ⁻¹ hf
    change IsInfiniteFinite F n U (determinantMul n χ⁻¹ (determinantMul n χ f)) at hi
    simpa only [determinantMul_inv_apply] using hi
  · exact isInfiniteFinite_determinantMultiplier n U χ

/-- Finite-order multiplication preserves every value's norm exactly. -/
theorem norm_evaluate_determinantMultiplier (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (f : ContinuousRationalFunctions F n) (g : AdelicGL F n) :
    ‖evaluate F n (determinantMultiplier n χ f) g‖ = ‖evaluate F n f g‖ := by
  rw [evaluate_determinantMultiplier, norm_mul, hχ.norm_adelicDeterminant, one_mul]

/-- The original growth constant and exponent work on every slice. -/
theorem hasPolynomialGrowth_determinantMultiplier_iff
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : ContinuousRationalFunctions F n) :
    HasPolynomialGrowth F n (determinantMultiplier n χ f) ↔
      HasPolynomialGrowth F n f := by
  unfold HasPolynomialGrowth ArchimedeanGL.HasPolynomialGrowth
  simp only [infiniteSlice, LinearMap.coe_mk, AddHom.coe_mk,
    norm_evaluate_determinantMultiplier n χ hχ]

private theorem finiteGrowthMultiplier_map_of_preserves
    (χ : HeckeCharacter F) (P : Submodule ℂ (ContinuousRationalFunctions F n))
    (hp : ∀ f ∈ P, determinantMultiplier n χ f ∈ P)
    (hi : ∀ f ∈ P, determinantMultiplier n χ⁻¹ f ∈ P) :
    P.map (determinantMultiplier n χ).toLinearMap = P := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hp g hg
  · intro hf
    refine ⟨determinantMultiplier n χ⁻¹ f, hi f hf, ?_⟩
    change determinantMul n χ (determinantMul n χ⁻¹ f) = f
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f

namespace InfiniteFiniteRationalFunctions

/-- Actual multiplication on functions finite under any specified infinite subgroup. -/
def determinantMultiplier (U : Subgroup (InfiniteAdelicGL F n)) (χ : HeckeCharacter F) :
    InfiniteFiniteRationalFunctions F n U ≃L[ℂ] InfiniteFiniteRationalFunctions F n U :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (finiteGrowthMultiplier_map_of_preserves n χ _
      (fun _ hf => isInfiniteFinite_determinantMultiplier n U χ hf)
      (fun _ hf => isInfiniteFinite_determinantMultiplier n U χ⁻¹ hf))

@[simp]
theorem evaluate_determinantMultiplier
    (U : Subgroup (InfiniteAdelicGL F n)) (χ : HeckeCharacter F)
    (f : InfiniteFiniteRationalFunctions F n U) (g : AdelicGL F n) :
    evaluate F n (determinantMultiplier n U χ f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

theorem infiniteRightAction_determinantMultiplier
    (U : Subgroup (InfiniteAdelicGL F n)) (χ : HeckeCharacter F) (k : U)
    (f : InfiniteFiniteRationalFunctions F n U) :
    infiniteFiniteRightAction F n U k (determinantMultiplier n U χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        determinantMultiplier n U χ (infiniteFiniteRightAction F n U k f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ _ f.val

theorem finiteRightAction_determinantMultiplier
    (U : Subgroup (InfiniteAdelicGL F n)) (χ : HeckeCharacter F) (d : FiniteAdelicGL F n)
    (f : InfiniteFiniteRationalFunctions F n U) :
    infiniteFiniteFiniteRightAction F n U d (determinantMultiplier n U χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        determinantMultiplier n U χ (infiniteFiniteFiniteRightAction F n U d f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ _ f.val

end InfiniteFiniteRationalFunctions

namespace PolynomialGrowthRationalFunctions

/-- Actual finite-order multiplication on the existing polynomial-growth space. -/
def finiteOrderDeterminantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    PolynomialGrowthRationalFunctions F n ≃L[ℂ] PolynomialGrowthRationalFunctions F n :=
  (ContinuousRationalFunctions.determinantMultiplier n χ).ofSubmodules _ _
    (finiteGrowthMultiplier_map_of_preserves n χ _
      (fun f hf => (mem_polynomialGrowthSubrepresentation F n _).mpr
        ((hasPolynomialGrowth_determinantMultiplier_iff n χ hχ f).mpr
          ((mem_polynomialGrowthSubrepresentation F n f).mp hf)))
      (fun f hf => (mem_polynomialGrowthSubrepresentation F n _).mpr
        ((hasPolynomialGrowth_determinantMultiplier_iff n χ⁻¹ hχ.inv f).mpr
          ((mem_polynomialGrowthSubrepresentation F n f).mp hf))))

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : PolynomialGrowthRationalFunctions F n) (g : AdelicGL F n) :
    evaluate F n (finiteOrderDeterminantMultiplier n χ hχ f).val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val g := rfl

theorem rightAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (g : AdelicGL F n)
    (f : PolynomialGrowthRationalFunctions F n) :
    polynomialGrowthRightAction F n g (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n g : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ (polynomialGrowthRightAction F n g f) := by
  apply Subtype.ext
  exact ContinuousRationalFunctions.determinantMultiplier_rightAction n χ g f.val

end PolynomialGrowthRationalFunctions
end Langlands.Automorphic
