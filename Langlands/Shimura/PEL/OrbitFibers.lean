import Langlands.Shimura.PEL.InvariantOrbits

/-! # Right translation inside a coarse orbit fiber -/

universe u v w

namespace Langlands.Shimura.PEL

variable {G : Type u} {Γ : Type v} {X : Type w}
variable [Group G] [Group Γ] [MulAction Gᵐᵒᵖ X] [MulAction Γ X]
variable [SMulCommClass Γ Gᵐᵒᵖ X]
variable {U V : Subgroup G}

namespace RightOrbit

/-- Equality after forgetting a fine orbit is witnessed by an actual coarse-level
translation. No freeness of the original action is required. -/
theorem exists_translate_of_forget_eq (hVU : V ≤ U)
    (hconj : ∀ u ∈ U, ∀ v ∈ V, u⁻¹ * v * u ∈ V)
    (x y : RightOrbit X V)
    (hxy : translate 1 (by intro v hv; simpa using hVU hv) x =
      translate 1 (by intro v hv; simpa using hVU hv) y) :
    ∃ u : G, ∃ hu : u ∈ U, translate u (hconj u hu) x = y := by
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      change mk U (right a 1) = mk U (right b 1) at hxy
      simp only [right_one] at hxy
      obtain ⟨u, hu, hb⟩ := (mk_eq_mk U a b).mp hxy
      refine ⟨u, hu, ?_⟩
      change mk V (right a u) = mk V b
      exact congrArg (mk V) hb.symm

end RightOrbit

namespace InvariantOrbit

/-- The actual same coarse-level element transports monodromy-invariant fine
orbits, because their equality is equality of the underlying right orbits. -/
theorem exists_translate_of_forget_eq (hVU : V ≤ U)
    (hconj : ∀ u ∈ U, ∀ v ∈ V, u⁻¹ * v * u ∈ V)
    (x y : InvariantOrbit (X := X) Γ V)
    (hxy : forget hVU x = forget hVU y) :
    ∃ u : G, ∃ hu : u ∈ U, translate u (hconj u hu) x = y := by
  obtain ⟨u, hu, h⟩ := RightOrbit.exists_translate_of_forget_eq hVU hconj
    x.val y.val (congrArg Subtype.val hxy)
  exact ⟨u, hu, Subtype.ext h⟩

end InvariantOrbit
end Langlands.Shimura.PEL
