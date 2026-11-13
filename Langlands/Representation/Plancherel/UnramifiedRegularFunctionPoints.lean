import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies
import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # Points of the algebra of regular functions on unramified characters

The evaluation-generated algebra `ℂ[X] = unramifiedRegularFunctions ν` separates the points of
`X = unramifiedCharacters ν`, and, when the common norm kernel is open, every `ℂ`-algebra
homomorphism `ℂ[X] → ℂ` is evaluation at an actual unramified character.
-/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel

universe uG uI

variable {G : Type uG} [Group G] [TopologicalSpace G] {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- Distinct unramified characters are separated by an evaluation `χ ↦ χ(g)`. -/
theorem unramifiedRegularFunctions_separates (χ χ' : unramifiedCharacters ν) (h : χ ≠ χ') :
    ∃ f ∈ unramifiedRegularFunctions ν, f χ ≠ f χ' := by
  have : ∃ g, (χ.val g : ℂ) ≠ χ'.val g := by
    by_contra hc
    push Not at hc
    exact h (Subtype.ext (ContinuousMonoidHom.ext fun g => Units.ext (hc g)))
  obtain ⟨g, hg⟩ := this
  exact ⟨unramifiedEvaluation ν g, Algebra.subset_adjoin ⟨g, rfl⟩, hg⟩

/-- Two `ℂ`-algebra homomorphisms out of `ℂ[X]` agreeing on the evaluations `χ ↦ χ(g)` are
equal. -/
theorem unramifiedRegularFunctions_algHom_ext {A : Type*} [Semiring A] [Algebra ℂ A]
    {φ ψ : unramifiedRegularFunctions ν →ₐ[ℂ] A}
    (h : ∀ g : G, φ (unramifiedEvaluationRegular ν g) = ψ (unramifiedEvaluationRegular ν g)) :
    φ = ψ := by
  ext ⟨f, hf⟩
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact h g
  | algebraMap c =>
    exact (φ.commutes c).trans (ψ.commutes c).symm
  | add x y hx hy ihx ihy =>
    have hsplit : (⟨x + y, (unramifiedRegularFunctions ν).add_mem hx hy⟩ :
        unramifiedRegularFunctions ν) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [hsplit, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
    have hsplit : (⟨x * y, (unramifiedRegularFunctions ν).mul_mem hx hy⟩ :
        unramifiedRegularFunctions ν) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [hsplit, map_mul, map_mul, ihx, ihy]

/-- When the common norm kernel is open, every `ℂ`-algebra homomorphism `ℂ[X] → ℂ` is
evaluation at an actual unramified character. -/
theorem unramifiedRegularFunctions_algHom_eq_eval [IsTopologicalGroup G]
    (hK : IsOpen (commonNormKernel ν : Set G))
    (ψ : unramifiedRegularFunctions ν →ₐ[ℂ] ℂ) :
    ∃ χ : unramifiedCharacters ν,
      ∀ f : unramifiedRegularFunctions ν, ψ f = (f : unramifiedCharacters ν → ℂ) χ := by
  let e := unramifiedEvaluationRegular ν
  have hunit : ∀ g : G, ψ (e g) * ψ (e g⁻¹) = 1 := by
    intro g
    rw [← map_mul, ← unramifiedEvaluationRegular_mul, mul_inv_cancel,
      unramifiedEvaluationRegular_one, map_one]
  let ω : G →* ℂˣ :=
    { toFun := fun g => ⟨ψ (e g), ψ (e g⁻¹), hunit g, by simpa using hunit g⁻¹⟩
      map_one' := by
        ext
        simp [e]
      map_mul' := by
        intro g h
        ext
        simp [e] }
  have hker : ∀ g ∈ commonNormKernel ν, ω g = 1 := by
    intro g hg
    have he : e g = 1 := by
      apply Subtype.ext
      funext χ
      have hχ : χ.val g = 1 := χ.2 hg
      simp [e, hχ]
    ext
    simp [ω, he]
  have hcont : Continuous ω := by
    refine continuous_of_continuousAt_one ω ?_
    have hev : (fun g => ω g) =ᶠ[nhds 1] fun _ => ω 1 := by
      filter_upwards [hK.mem_nhds (commonNormKernel ν).one_mem] with g hg
      rw [hker g hg, map_one]
    exact (continuousAt_const).congr hev.symm
  let χ : unramifiedCharacters ν := ⟨⟨ω, hcont⟩, fun g hg => hker g hg⟩
  refine ⟨χ, fun f => ?_⟩
  have := unramifiedRegularFunctions_algHom_ext ν
    (φ := ψ) (ψ := (Pi.evalAlgHom ℂ (fun _ : unramifiedCharacters ν => ℂ) χ).comp
      (unramifiedRegularFunctions ν).val) (fun g => rfl)
  exact congrArg (fun φ => φ f) this

end Langlands.Plancherel
