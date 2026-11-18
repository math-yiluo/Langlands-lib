import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Tactic.LinearCombination

/-! # Real characters as a fixed cocharacter sign times a norm -/

noncomputable section

namespace Langlands.GroupScheme.RealTorus

open Complex
open scoped ComplexConjugate

universe u

/-- On a free abelian character lattice with an involution, every equivariant complex
point is the product of a fixed integral cocharacter evaluated at `-1` and a norm. -/
def CharacterNormDecompositionStatement : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module.Free ℤ M]
    (s : M ≃+ M), Function.Involutive s →
    ∀ (x : Multiplicative M →* ℂˣ),
      (∀ m : M, (x (Multiplicative.ofAdd (s m)) : ℂ) = conj (x (Multiplicative.ofAdd m) : ℂ)) →
      ∃ (d : M →+ ℤ) (y : Multiplicative M →* ℂˣ),
        (∀ m, d (s m) = d m) ∧
        ∀ m : M, (x (Multiplicative.ofAdd m) : ℂ) =
          (-1 : ℂ) ^ d m * (y (Multiplicative.ofAdd m) : ℂ) *
            conj (y (Multiplicative.ofAdd (s m)) : ℂ)

private def expUnits : Multiplicative ℂ →* ℂˣ where
  toFun z := Units.mk0 (exp z.toAdd) (exp_ne_zero _)
  map_one' := Units.ext exp_zero
  map_mul' z w := Units.ext (exp_add (x := z.toAdd) (y := w.toAdd))

private theorem exists_logarithm {M : Type u} [AddCommGroup M] [Module.Free ℤ M]
    (x : Multiplicative M →* ℂˣ) :
    ∃ L : M →ₗ[ℤ] ℂ, ∀ m : M, exp (L m) = (x (Multiplicative.ofAdd m) : ℂ) := by
  let b := Module.Free.chooseBasis ℤ M
  let L := b.constr ℤ (fun i => log (x (Multiplicative.ofAdd (b i)) : ℂ))
  let e := expUnits.comp L.toAddMonoidHom.toMultiplicative
  have he : e = x := by
    apply MonoidHom.toAdditiveRight.injective
    apply AddMonoidHom.toIntLinearMap_injective
    apply b.ext
    intro i
    apply congrArg Additive.ofMul
    apply Units.ext
    change exp (L (b i)) = (x (Multiplicative.ofAdd (b i)) : ℂ)
    rw [show L (b i) = log (x (Multiplicative.ofAdd (b i)) : ℂ) from b.constr_basis ℤ _ i]
    exact exp_log (x (Multiplicative.ofAdd (b i))).ne_zero
  exact ⟨L, fun m => congrArg (fun f : Multiplicative M →* ℂˣ =>
    (f (Multiplicative.ofAdd m) : ℂ)) he⟩

/-- Lift to an additive logarithm, then measure its conjugation defect in multiples of `2πi`. -/
theorem characterNormDecomposition : CharacterNormDecompositionStatement.{u} := by
  intro M _ _ s hs x hx
  obtain ⟨L, hL⟩ := exists_logarithm x
  let D := L.toAddMonoidHom -
    (starRingEnd ℂ).toAddMonoidHom.comp (L.toAddMonoidHom.comp s.toAddMonoidHom)
  let P := 2 * (Real.pi : ℂ) * I
  have hP : P ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hperiod (m : M) : ∃ n : ℤ, D m = (n : ℂ) * P := by
    apply exp_eq_one_iff.mp
    change exp (L m - conj (L (s m))) = 1
    rw [exp_sub, hL m, exp_conj, hL (s m), hx m]
    simp only [starRingEnd_apply, star_star]
    exact div_self (x (Multiplicative.ofAdd m)).ne_zero
  choose d hd using hperiod
  have hcancel (a b : ℤ) (h : (a : ℂ) * P = (b : ℂ) * P) : a = b :=
    Int.cast_injective (mul_right_cancel₀ hP h)
  let dHom : M →+ ℤ :=
    { toFun := d
      map_zero' := by
        apply hcancel
        rw [← hd, map_zero, Int.cast_zero, zero_mul]
      map_add' := by
        intro a b
        apply hcancel
        rw [← hd, Int.cast_add, add_mul, ← hd, ← hd, map_add] }
  let half : M →ₗ[ℤ] ℂ := (2 : ℂ)⁻¹ • L
  let y := expUnits.comp half.toAddMonoidHom.toMultiplicative
  refine ⟨dHom, y, ?_, ?_⟩
  · intro m
    change d (s m) = d m
    apply hcancel
    rw [← hd (s m)]
    calc
      D (s m) = -conj (D m) := by
        change L (s m) - conj (L (s (s m))) = -conj (L m - conj (L (s m)))
        rw [hs m, map_sub]
        simp only [starRingEnd_apply, star_star, neg_sub]
      _ = (d m : ℂ) * P := by
        rw [hd m]
        simp [P, map_mul, map_ofNat]
  · intro m
    have hEq : L m = (d m : ℂ) * ((Real.pi : ℂ) * I) + half m + conj (half (s m)) := by
      have hm := hd m
      change L m - conj (L (s m)) = (d m : ℂ) * (2 * (Real.pi : ℂ) * I) at hm
      change L m = _ + (2 : ℂ)⁻¹ * L m + conj ((2 : ℂ)⁻¹ * L (s m))
      rw [map_mul, map_inv₀, map_ofNat]
      linear_combination hm / 2
    change (x (Multiplicative.ofAdd m) : ℂ) =
      (-1 : ℂ) ^ d m * exp (half m) * conj (exp (half (s m)))
    rw [← hL m, hEq, exp_add, exp_add, exp_int_mul, exp_pi_mul_I, exp_conj]

end Langlands.GroupScheme.RealTorus
