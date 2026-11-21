import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Lean.Elab.Tactic.Omega

namespace Langlands.BaseChange

open Multiplicative
open scoped BigOperators

/-- Integer weights in strictly decreasing order. -/
abbrev StrictWeight (n : ℕ) := {w : Fin n → ℤ // StrictAnti w}

/-- A multiplicative character of the additive integer weight lattice. -/
abbrev WeightCharacter (n : ℕ) (R : Type*) [MulOneClass R] :=
  Multiplicative (Fin n → ℤ) →* R

private def weightSlope (n : ℕ) : Fin n → ℤ := fun i ↦ -(i.val : ℤ)

private theorem strictAnti_weightSlope (n : ℕ) : StrictAnti (weightSlope n) := by
  intro i j hij
  exact neg_lt_neg (Int.ofNat_lt.mpr (Fin.lt_def.mp hij))

private def antitoneWeights (n : ℕ) : Submonoid (Multiplicative (Fin n → ℤ)) where
  carrier := {w | Antitone (toAdd w)}
  one_mem' := antitone_const
  mul_mem' := by
    intro x y hx hy i j hij
    exact add_le_add (hx hij) (hy hij)

private theorem exists_antitone_translate {n : ℕ} (x : Fin n → ℤ) :
    ∃ z : antitoneWeights n, ofAdd x * (z : Multiplicative (Fin n → ℤ)) ∈ antitoneWeights n := by
  let bound : ℤ := ∑ i, |x i|
  have hbound (i : Fin n) : |x i| ≤ bound :=
    Finset.single_le_sum (f := fun j ↦ |x j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)
  have hb : 0 ≤ bound := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  let step := 2 * bound + 1
  have hs : 0 ≤ step := by dsimp [step]; omega
  let z : Fin n → ℤ := fun i ↦ step * weightSlope n i
  have hgap {i j : Fin n} (hij : i < j) : step ≤ z i - z j := by
    have h := strictAnti_weightSlope n hij
    have hdiff : 1 ≤ weightSlope n i - weightSlope n j := by omega
    simpa only [z, mul_sub, mul_one] using mul_le_mul_of_nonneg_left hdiff hs
  have hz : Antitone z := antitone_iff_forall_lt.mpr fun _ _ hij ↦ by
    have h := hgap hij
    omega
  refine ⟨⟨ofAdd z, hz⟩, ?_⟩
  change Antitone (x + z)
  intro i j hij
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  change x j + z j ≤ x i + z i
  have hji := (abs_le.mp (hbound j)).2
  have hii := (abs_le.mp (hbound i)).1
  have h := hgap hij
  dsimp [step] at h
  omega

variable {R : Type*} [CommRing R] [IsDomain R]

private theorem character_ne_zero {G : Type*} [Group G] (χ : G →* R) (g : G) : χ g ≠ 0 := by
  intro hg
  simpa [hg] using (χ.map_mul g g⁻¹).symm

private theorem restrict_antitoneWeights_injective (n : ℕ) :
    Function.Injective
      (fun χ : WeightCharacter n R ↦ χ.comp (antitoneWeights n).subtype) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro g
  obtain ⟨z, hz⟩ := exists_antitone_translate (toAdd g)
  have h₁ : χ z.1 = ψ z.1 := DFunLike.congr_fun h z
  have h₂ : χ (g * z.1) = ψ (g * z.1) := DFunLike.congr_fun h ⟨g * z.1, hz⟩
  rw [map_mul, map_mul, ← h₁] at h₂
  exact mul_right_cancel₀ (character_ne_zero χ z.1) h₂

/-- Distinct characters of the integer weight lattice are linearly independent on the strictly
decreasing weights. -/
theorem linearIndependent_strictWeightCharacters (n : ℕ) :
    LinearIndependent R
      (fun (χ : WeightCharacter n R) (w : StrictWeight n) ↦ χ (ofAdd w.1)) := by
  have hweak := (linearIndependent_monoidHom (antitoneWeights n) R).comp _
    (restrict_antitoneWeights_injective (R := R) n)
  apply linearIndependent_iff'.mpr
  intro s coefficient h i hi
  have htranslated :
      ∑ χ ∈ s, (coefficient χ * χ (ofAdd (weightSlope n))) •
        (fun w : antitoneWeights n ↦ χ w) = 0 := by
    funext w
    have hw : StrictAnti (weightSlope n + toAdd w.1) := by
      intro a b hab
      exact add_lt_add_of_lt_of_le (strictAnti_weightSlope n hab) (w.2 hab.le)
    have heval := congr_fun h ⟨weightSlope n + toAdd w.1, hw⟩
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      ofAdd_add, ofAdd_toAdd, map_mul, mul_assoc] using heval
  exact (mul_eq_zero.mp ((linearIndependent_iff'.mp hweak) s _ htranslated i hi)).resolve_right
    (character_ne_zero i (ofAdd (weightSlope n)))

/-- Evaluate a finite linear combination of weight characters on the strict weights. -/
noncomputable def strictWeightCharacterEvaluation (n : ℕ) :
    (WeightCharacter n R →₀ R) →ₗ[R] (StrictWeight n → R) :=
  Finsupp.linearCombination R (fun χ w ↦ χ (ofAdd w.1))

/-- Equality of finite character sums on the strict weights determines their coefficients,
even with a common nonzero weight-dependent scalar. -/
theorem strictWeightCharacterCoefficients_eq {n : ℕ} (factor : StrictWeight n → R)
    (hne : ∀ w, factor w ≠ 0) (a b : WeightCharacter n R →₀ R)
    (heq : ∀ w, factor w * strictWeightCharacterEvaluation n a w =
      factor w * strictWeightCharacterEvaluation n b w) : a = b := by
  have h : strictWeightCharacterEvaluation n a = strictWeightCharacterEvaluation n b :=
    funext fun w ↦ mul_left_cancel₀ (hne w) (heq w)
  apply sub_eq_zero.mp
  apply (linearIndependent_iff.mp (linearIndependent_strictWeightCharacters (R := R) n))
  show strictWeightCharacterEvaluation n (a - b) = 0
  rw [map_sub, h, sub_self]

end Langlands.BaseChange
