import Langlands.Correspondence.HenniartLadicStatement
import Langlands.Galois.Local.TameFrobenius
import Langlands.Representation.LadicMonodromy

/-! # Finite inertia image of irreducible ℓ-adic Galois representations -/

noncomputable section

namespace Langlands.Henniart

open ValuativeRel LocalNumerical
open Langlands.LocalGalois.SepClosed (absoluteInertia)

universe uK uΩ uW

/-- For `ℓ` different from the residue characteristic, an irreducible continuous ℓ-adic
representation of the Galois group of a nonarchimedean local field has finite image on
inertia. -/
theorem ladicFiniteInertia : LadicFiniteInertiaStatement.{uK, uΩ, uW} := by
  intro K _ _ _ _ Ω _ _ _ ℓ _ hℓp _ι A hcont _hdef hirr
  obtain ⟨φ, hφ⟩ := LocalGalois.SepClosed.exists_tameFrobenius K Ω
  have hℓ : ℓ.Prime := Fact.out
  have hp : (ringChar 𝓀[K]).Prime := CharP.char_is_prime 𝓀[K] _
  have hcop : Nat.Coprime ℓ (ringChar 𝓀[K]) := by
    rw [Nat.coprime_primes hℓ hp]
    intro h
    apply hℓp
    rw [h]
    exact ringChar.Nat.cast_ringChar
  have hq : 2 ≤ Nat.card 𝓀[K] := Finite.one_lt_card
  have hℓ0 : ((ℓ : ℕ) : PadicAlgCl ℓ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hℓ1 : ‖((ℓ : ℕ) : PadicAlgCl ℓ)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  refine LadicMonodromy.finite_image_of_tameFrobenius hℓ hcop hq hℓ0 hℓ1
    (absoluteInertia K Ω) φ (LocalGalois.SepClosed.exists_normal_finiteIndex_subset K Ω) hφ
    A.representation hcont ?_
  intro W hW
  rcases hirr.eq_bot_or_eq_top ⟨W, fun g => fun ⦃v⦄ hv => hW g v hv⟩ with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

end Langlands.Henniart
