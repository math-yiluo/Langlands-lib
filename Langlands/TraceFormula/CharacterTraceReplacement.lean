import Langlands.TraceFormula.BoundedCharacterSeparationProof
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # Trace replacement after bounded character separation -/

universe u v w uA uB

namespace Langlands.TraceFormula

/-- Separate a summable trace identity by its character families, perform a
replacement on each fibre, and reassemble the identity with the same character
tests. The complex coefficients may carry signs from an ordinary and a twisted sum. -/
def CharacterTraceReplacementStatement : Prop :=
  ∀ (ι : Type u) (W : Type v) (H : W → Type w) [∀ x, Semiring (H x)] [∀ x, Algebra ℂ (H x)]
    (χ : ι → (x : W) → H x →ₐ[ℂ] ℂ)
    (A : Type uA) (B : Type uB) (elementary : A → ι → ℂ) (replacement : B → ι → ℂ),
    (∀ (x : W) (h : H x), ∃ C : ℝ, ∀ i, ‖χ i x h‖ ≤ C) →
    (∀ (x : W) (h : H x), ∃ h' : H x, ∀ i, χ i x h' = starRingEnd ℂ (χ i x h)) →
    (∀ a, Summable (elementary a)) →
    (∀ (a : A) (S : Finset W) (h : (x : W) → H x),
      HasSum (fun i => elementary a i * ∏ x ∈ S, χ i x (h x)) 0) →
    (∀ i₀ : ι, let Fibre := {i : ι // ∀ x, χ i x = χ i₀ x}
      (∀ a, HasSum (fun i : Fibre => elementary a i.val) 0) →
      ∀ b, HasSum (fun i : Fibre => replacement b i.val) 0) →
    (∀ b, Summable (replacement b)) →
    ∀ (b : B) (S : Finset W) (h : (x : W) → H x),
      HasSum (fun i => replacement b i * ∏ x ∈ S, χ i x (h x)) 0

set_option maxHeartbeats 800000 in
theorem characterTraceReplacement : CharacterTraceReplacementStatement.{u,v,w,uA,uB} := by
  classical
  intro ι W H _ _ χ A B elementary replacement hbound hconj hsum hvanish hreplace
    hsumReplacement b S h
  let c := fun i => replacement b i * ∏ x ∈ S, χ i x (h x)
  choose bounds hbounds using fun x : W => hbound x (h x)
  let C := ∏ x ∈ S, max (bounds x) 0
  have hc : Summable c := by
    refine ((hsumReplacement b).norm.mul_right C).of_norm_bounded (fun i => ?_)
    change ‖replacement b i * ∏ x ∈ S, χ i x (h x)‖ ≤ ‖replacement b i‖ * C
    simp only [norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) ?_)
      (norm_nonneg _)
    exact fun x _ => (hbounds x i).trans (le_max_left _ _)
  have hfibre (ω : (x : W) → H x →ₐ[ℂ] ℂ) : (∑' i : χ ⁻¹' {ω}, c i.val) = 0 := by
    by_cases he : ω ∈ Set.range χ
    · obtain ⟨i₀, rfl⟩ := he
      have hequiv (i : ι) : (∀ x, χ i x = χ i₀ x) ↔ i ∈ χ ⁻¹' {χ i₀} :=
        ⟨funext, fun hi x => congrFun hi x⟩
      let e := Equiv.subtypeEquivRight hequiv
      have helementary (a : A) : HasSum (fun i : {i : ι // ∀ x, χ i x = χ i₀ x} =>
          elementary a i.val) 0 :=
        boundedCharacterSeparation ι W H χ (elementary a) (hsum a) hbound hconj (hvanish a) i₀
      have hlocal := (hreplace i₀ helementary b).mul_right (∏ x ∈ S, χ i₀ x (h x))
      have hweighted : (fun i : {i : ι // ∀ x, χ i x = χ i₀ x} => c (e i).val) =
          fun i => replacement b i.val * ∏ x ∈ S, χ i₀ x (h x) := by
        funext i
        change replacement b i.val * ∏ x ∈ S, χ i.val x (h x) = _
        rw [show χ i.val = χ i₀ from funext i.property]
      have hz : HasSum (fun i : {i : ι // ∀ x, χ i x = χ i₀ x} => c (e i).val) 0 := by
        rw [hweighted]
        simpa only [zero_mul] using hlocal
      have hf : HasSum (fun i : χ ⁻¹' {χ i₀} => c i.val) 0 :=
        e.hasSum_iff.mp hz
      exact hf.tsum_eq
    · let : IsEmpty (χ ⁻¹' {ω} : Set ι) := ⟨fun i => he ⟨i.val, i.property⟩⟩
      simp
  have hg := hc.hasSum.tsum_fiberwise χ
  have hzero : (∑' ω, ∑' i : χ ⁻¹' {ω}, c i.val) = 0 := by simp only [hfibre, tsum_zero]
  exact (hg.tsum_eq.symm.trans hzero) ▸ hc.hasSum

end Langlands.TraceFormula
