import Langlands.Representation.Derivative.MirabolicRankOneDetectionStatement

/-!
# Proof of the rank-one boundary of mirabolic derivative detection

The radical of `P_1` is trivial, so every trivial-character relation `π(u)v - v`
vanishes. The actual `Ψ⁻` quotient map at rank one therefore has zero kernel, and a
subsingleton quotient carrier forces a subsingleton source carrier.
-/

noncomputable section

namespace Langlands.Derivative

open GeneralLinear GeneralLinear.Mirabolic

universe uF uV

namespace Mirabolic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The trivial-character relations of the rank-one radical are zero. -/
theorem relations_rankOne_eq_bot (T : F.TopologicalData) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier),
      Jacquet.Localization.relations A.representation (radical 0 F.Carrier) 1 = ⊥ := by
  let _ := T.topology
  intro A
  rw [eq_bot_iff, Jacquet.Localization.relations, Submodule.span_le]
  rintro _ ⟨⟨u, v⟩, rfl⟩
  obtain rfl : u = 1 := @Subsingleton.elim _ radical_rankOneSubsingleton u 1
  simp only [Nat.reduceAdd, Submodule.bot_coe, OneMemClass.coe_one, map_one,
    Module.End.one_apply, Units.val_one, one_smul, sub_self,
    Set.mem_singleton_iff]

/-- The actual `Ψ⁻` quotient map from `P_1` to `GL_0` is injective. -/
theorem psiMinusQuotient_rankOne_injective (T : F.TopologicalData) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier),
      Function.Injective (psiMinusQuotient T 0 A) := by
  let _ := T.topology
  intro A
  rw [← LinearMap.ker_eq_bot, ker_psiMinusQuotient T 0 A]
  exact relations_rankOne_eq_bot T A

end Mirabolic

/-- The actual normalized `Ψ⁻` from `P_1` to `GL_0` detects vanishing. -/
theorem mirabolicRankOneDetection {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicRankOneDetection.{uF, uV} F T := by
  let _ := T.topology
  intro A hA
  have : Subsingleton
      (Jacquet.Localization.Coinvariants A.representation (radical 0 F.Carrier) 1) := hA
  exact (Mirabolic.psiMinusQuotient_rankOne_injective T A).subsingleton

end Langlands.Derivative
