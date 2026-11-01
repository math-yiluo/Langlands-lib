import Langlands.Shimura.PEL.OrbitFibers

/-! # Coset detection for free right actions on level orbits -/

universe u v w

namespace Langlands.Shimura.PEL

variable {G : Type u} {Γ : Type v} {X : Type w}
variable [Group G] [MulAction Gᵐᵒᵖ X]
variable {U V : Subgroup G}

namespace RightOrbit

/-- For a free right action, two transporter translations of the same orbit
agree exactly when their elements have the same right target coset. -/
theorem translate_eq_translate_iff
    (hfree : ∀ x : X, Function.Injective (right x : G → X))
    (g h : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V)
    (hh : ∀ u ∈ U, h⁻¹ * u * h ∈ V) (q : RightOrbit X U) :
    translate g hg q = translate h hh q ↔ g⁻¹ * h ∈ V := by
  induction q using Quotient.inductionOn with
  | h x =>
    change mk V (right x g) = mk V (right x h) ↔ g⁻¹ * h ∈ V
    constructor
    · intro heq
      obtain ⟨a, ha, hxa⟩ := (mk_eq_mk V _ _).mp heq
      have hga : h = g * a := hfree x (hxa.trans (right_mul x g a))
      simpa [hga] using ha
    · intro hgh
      apply (mk_eq_mk V _ _).mpr
      refine ⟨g⁻¹ * h, hgh, ?_⟩
      simp [right_mul]

/-- The stabilizer of an orbit under free right translation is the actual
level subgroup. -/
theorem translate_eq_self_iff
    (hfree : ∀ x : X, Function.Injective (right x : G → X))
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U) (q : RightOrbit X U) :
    translate g hg q = q ↔ g ∈ U := by
  have heq := translate_eq_translate_iff hfree g 1 hg
    (by intro u hu; simpa using hu) q
  simpa only [translate_one, mul_one, Subgroup.inv_mem_iff] using heq

end RightOrbit

variable [Group Γ] [MulAction Γ X] [SMulCommClass Γ Gᵐᵒᵖ X]

namespace InvariantOrbit

/-- Monodromy-fixed orbit equality detects precisely the same actual target
coset when the action on frames is free. -/
theorem translate_eq_translate_iff
    (hfree : ∀ x : X, Function.Injective (right x : G → X))
    (g h : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ V)
    (hh : ∀ u ∈ U, h⁻¹ * u * h ∈ V)
    (q : InvariantOrbit (X := X) Γ U) :
    translate g hg q = translate h hh q ↔ g⁻¹ * h ∈ V := by
  constructor
  · intro heq
    exact (RightOrbit.translate_eq_translate_iff hfree g h hg hh q.val).mp
      (congrArg Subtype.val heq)
  · intro hgh
    exact Subtype.ext
      ((RightOrbit.translate_eq_translate_iff hfree g h hg hh q.val).mpr hgh)

/-- The monodromy condition introduces no extra right stabilizer of a fixed
orbit when the right action on frames is free. -/
theorem translate_eq_self_iff
    (hfree : ∀ x : X, Function.Injective (right x : G → X))
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U)
    (q : InvariantOrbit (X := X) Γ U) :
    translate g hg q = q ↔ g ∈ U := by
  constructor
  · intro heq
    exact (RightOrbit.translate_eq_self_iff hfree g hg q.val).mp
      (congrArg Subtype.val heq)
  · intro hmem
    exact Subtype.ext ((RightOrbit.translate_eq_self_iff hfree g hg q.val).mpr hmem)

end InvariantOrbit
end Langlands.Shimura.PEL
