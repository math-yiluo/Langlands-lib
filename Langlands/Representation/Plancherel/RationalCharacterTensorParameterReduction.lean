import Langlands.Representation.Plancherel.RationalCharacterTensorParameterStatement
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Linear algebra of the rational-character tensor parameter

The canonical map `ℂ ⊗[ℤ] X^*(G) → Hom(Λ(G), ℂ)` is surjective for every
connected reductive group over a nonarchimedean local field, because `ℂ` is a
divisible abelian group. It is injective as soon as every nonzero rational
character has a nonzero valuation at some rational point.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Valuation detection: every nonzero rational character has a nonzero
integer valuation at some rational point. -/
def RationalValuationDetects : Prop :=
  ∀ χ : GroupScheme.rationalCharacters G, χ ≠ 0 →
    ∃ g : GroupScheme.rationalPoints G, (rationalCharacterValuation G g).toAdd χ ≠ 0

/-- Evaluation formula for tensors written on the double integer dual of the
characters: reflexivity returns them to `ℂ ⊗ X^*(G)`. -/
theorem rationalCharacterTensorParameter_comm_rTensor_evalEquiv
    [Module.Free ℤ (GroupScheme.rationalCharacters G)]
    [Module.Finite ℤ (GroupScheme.rationalCharacters G)]
    (t : Module.Dual ℤ (Module.Dual ℤ (GroupScheme.rationalCharacters G)) ⊗[ℤ] ℂ)
    (a : Additive (rationalDiscreteValuationImage G)) :
    rationalCharacterTensorParameter G
        (TensorProduct.comm ℤ _ _
          (((Module.evalEquiv ℤ (GroupScheme.rationalCharacters G)).symm.toLinearMap.rTensor
            ℂ) t)) a =
      dualTensorHom ℤ (Module.Dual ℤ (GroupScheme.rationalCharacters G)) ℂ t
        (rationalImageIntegerDual G a) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ c =>
    obtain ⟨χ, rfl⟩ := (Module.evalEquiv ℤ (GroupScheme.rationalCharacters G)).surjective φ
    rw [LinearMap.rTensor_tmul, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      TensorProduct.comm_tmul, dualTensorHom_apply, Module.evalEquiv_apply,
      Module.Dual.eval_apply]
    change c * ((Additive.toMul a).val.toAdd χ : ℂ) = _
    rw [zsmul_eq_mul, mul_comm]
    rfl
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, LinearMap.add_apply, hx, hy]

/-- Surjectivity holds unconditionally: functionals on the actual valuation
image extend to the integer dual of the characters because `ℂ` is divisible. -/
theorem rationalCharacterTensorParameter_surjective
    (hG : GroupScheme.IsConnectedReductive G) :
    Function.Surjective (rationalCharacterTensorParameter G) := by
  have hX := GroupScheme.rationalCharacterLattice F G hG
  have := hX.1
  have := hX.2
  intro f
  let : DivisibleBy ℂ ℤ := divisibleByIntOfCharZero
  obtain ⟨f', hf'⟩ := (Module.Baer.of_divisible ℂ).extension_property_addMonoidHom
    (rationalImageIntegerDual G).toAddMonoidHom (rationalImageIntegerDual_injective G) f
  obtain ⟨t, ht⟩ := (dualTensorHomEquiv ℤ
    (Module.Dual ℤ (GroupScheme.rationalCharacters G)) ℂ).surjective f'.toIntLinearMap
  refine ⟨TensorProduct.comm ℤ _ _
    (((Module.evalEquiv ℤ (GroupScheme.rationalCharacters G)).symm.toLinearMap.rTensor ℂ) t),
    ?_⟩
  refine AddMonoidHom.ext fun a => ?_
  rw [rationalCharacterTensorParameter_comm_rTensor_evalEquiv]
  change dualTensorHomEquiv ℤ _ ℂ t _ = _
  rw [ht]
  exact DFunLike.congr_fun hf' a

/-- The tensor parameter factors through the character-to-functional pairing
on the actual valuation image. -/
theorem rationalCharacterTensorParameter_apply_eq_dualTensorHom
    (t : ℂ ⊗[ℤ] GroupScheme.rationalCharacters G)
    (a : Additive (rationalDiscreteValuationImage G)) :
    rationalCharacterTensorParameter G t a =
      dualTensorHom ℤ (Additive (rationalDiscreteValuationImage G)) ℂ
        (TensorProduct.comm ℤ _ _ (((rationalImageIntegerDual G).flip.lTensor ℂ) t)) a := by
  induction t using TensorProduct.inductionOn with
  | tmul c χ =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.comm_tmul, dualTensorHom_apply,
      LinearMap.flip_apply]
    change c * ((Additive.toMul a).val.toAdd χ : ℂ) = _
    rw [zsmul_eq_mul, mul_comm]
    rfl
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, LinearMap.add_apply, hx, hy]

/-- Valuation detection makes the character-to-functional pairing injective. -/
theorem rationalImageIntegerDual_flip_injective (h : RationalValuationDetects G) :
    Function.Injective (rationalImageIntegerDual G).flip := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro χ hχ
  by_contra hne
  obtain ⟨g, hg⟩ := h χ hne
  apply hg
  have := DFunLike.congr_fun hχ
    (Additive.ofMul (⟨rationalCharacterValuation G g, g, rfl⟩ : rationalDiscreteValuationImage G))
  exact this

/-- Injectivity under valuation detection, by flatness of `ℂ` over `ℤ`. -/
theorem rationalCharacterTensorParameter_injective_of_detects
    (hG : GroupScheme.IsConnectedReductive G) (h : RationalValuationDetects G) :
    Function.Injective (rationalCharacterTensorParameter G) := by
  obtain ⟨hΛ₁, hΛ₂⟩ := rationalReductiveImage_free_finite G hG
  intro t t' htt'
  have hflat : Function.Injective ((rationalImageIntegerDual G).flip.lTensor ℂ) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (rationalImageIntegerDual_flip_injective G h)
  apply hflat
  apply (TensorProduct.comm ℤ _ _).injective
  apply (dualTensorHomEquiv ℤ (Additive (rationalDiscreteValuationImage G)) ℂ).injective
  ext a
  change dualTensorHom ℤ _ ℂ _ a = dualTensorHom ℤ _ ℂ _ a
  rw [← rationalCharacterTensorParameter_apply_eq_dualTensorHom,
    ← rationalCharacterTensorParameter_apply_eq_dualTensorHom, htt']

/-- Bijectivity under valuation detection. -/
theorem rationalCharacterTensorParameter_bijective_of_detects
    (hG : GroupScheme.IsConnectedReductive G) (h : RationalValuationDetects G) :
    Function.Bijective (rationalCharacterTensorParameter G) :=
  ⟨rationalCharacterTensorParameter_injective_of_detects G hG h,
    rationalCharacterTensorParameter_surjective G hG⟩

/-- The target statement follows from valuation detection for every connected
reductive group over every nonarchimedean local field. -/
theorem rationalCharacterTensorParameterStatement_of_detects
    (h : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F))),
      GroupScheme.IsConnectedReductive G → RationalValuationDetects G) :
    RationalCharacterTensorParameterStatement.{u} := by
  intro F _ _ _ _ G hG
  exact rationalCharacterTensorParameter_bijective_of_detects G hG (h F G hG)

end Langlands.Plancherel
