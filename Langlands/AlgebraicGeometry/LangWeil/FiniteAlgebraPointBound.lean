import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.SetTheory.Cardinal.Finite

/-! # Uniform field-valued point bounds for module-finite algebras -/

universe u v w

namespace Langlands.AlgebraicGeometry.LangWeil

open Polynomial

/-- A module-finite algebra admits a uniform bound on its homomorphisms to any field,
independent of both the field and its algebra structure over the base. -/
theorem exists_uniform_card_algHom_le (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] :
    ∃ N : ℕ, ∀ (K : Type w) [Field K] [Algebra R K],
      Finite (A →ₐ[R] K) ∧ Nat.card (A →ₐ[R] K) ≤ N := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R A).out
  have hp (a : s) : ∃ p : R[X], p.Monic ∧ aeval (a : A) p = 0 :=
    (Algebra.IsIntegral.isIntegral (a : A))
  choose p hpmon hpzero using hp
  refine ⟨∏ a : s, (p a).natDegree, ?_⟩
  intro K _ _
  let ev : (A →ₐ[R] K) → ((a : s) → (p a).rootSet K) := fun φ a =>
    ⟨φ (a : A), (hpmon a).mem_rootSet.mpr (by
      rw [aeval_algHom_apply, hpzero a, map_zero])⟩
  have hev : Function.Injective ev := by
    intro φ ψ h
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro a ha
    exact congrArg Subtype.val (congrFun h ⟨a, ha⟩)
  refine ⟨Finite.of_injective ev hev, ?_⟩
  calc
    Nat.card (A →ₐ[R] K) ≤ Nat.card ((a : s) → (p a).rootSet K) :=
      Nat.card_le_card_of_injective ev hev
    _ = ∏ a : s, Nat.card ((p a).rootSet K) := Nat.card_pi
    _ ≤ ∏ a : s, (p a).natDegree :=
      Finset.prod_le_prod fun a _ => ncard_rootSet_le (p a) K

end Langlands.AlgebraicGeometry.LangWeil
