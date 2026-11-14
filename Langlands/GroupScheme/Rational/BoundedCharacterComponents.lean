import Langlands.GroupScheme.Rational.SplitTorusRationalDetection
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Character components of bounded functions -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.BoundedCharacterComponents

section Characters

variable {K : Type u} [Field K] {H : Type v} [Monoid H] {ι : Type w}

/-- A translation-invariant subspace of functions contains each distinct
character component of every finite character sum it contains. -/
theorem character_component_mem
    (M : Submodule K (H → K))
    (hM : ∀ f ∈ M, ∀ t : H, (fun x => f (t * x)) ∈ M)
    (χ : ι → H →* K) (hχ : Function.Injective χ)
    (s : Finset ι) (c : ι → K)
    (hs : (∑ i ∈ s, c i • (χ i : H → K)) ∈ M) :
    ∀ i ∈ s, c i • (χ i : H → K) ∈ M := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | @insert a s ha ih =>
    have hsmall : ∀ i ∈ s, c i • (χ i : H → K) ∈ M := by
      intro i hi
      have hia : i ≠ a := by
        intro h
        subst i
        exact ha hi
      have hne : χ i ≠ χ a := fun h => hia (hχ h)
      obtain ⟨t, ht⟩ : ∃ t : H, χ i t ≠ χ a t := by
        by_contra h
        apply hne
        ext t
        exact not_ne_iff.mp (not_exists.mp h t)
      let d : ι → K := fun j => c j * (χ j t - χ a t)
      have hd : (∑ j ∈ s, d j • (χ j : H → K)) ∈ M := by
        have hm := M.sub_mem (hM _ hs t) (M.smul_mem (χ a t) hs)
        convert hm using 1
        funext x
        simp only [Finset.sum_insert ha, Finset.sum_apply, Pi.add_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul, d]
        simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
        have hsum : (∑ j ∈ s, c j * χ a t * χ j x) =
            χ a t * ∑ j ∈ s, c j * χ j x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hsum]
        ring
      have hi' := ih d hd i hi
      have hrecover :
          c i • (χ i : H → K) =
            (χ i t - χ a t)⁻¹ • (d i • (χ i : H → K)) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, d]
        field_simp
      rw [hrecover]
      exact M.smul_mem _ hi'
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hrest : (∑ j ∈ s, c j • (χ j : H → K)) ∈ M :=
        M.sum_mem fun j hj => hsmall j hj
      have hm := M.sub_mem hs hrest
      simpa only [Finset.sum_insert ha, add_sub_cancel_right] using hm
    · exact hsmall i hi

end Characters

section BoundedFunctions

variable {K : Type u} [Field K] [ValuativeRel K] {H : Type v} [Monoid H]

/-- Functions with a uniform nonzero valuative upper bound. -/
def boundedFunctions : Submodule K (H → K) :=
  (boundedEvaluationSubalgebra
    (fun h : H => Pi.evalAlgHom K (fun _ : H => K) h)).toSubmodule

theorem boundedFunctions_translate (f : H → K) (hf : f ∈ boundedFunctions)
    (t : H) : (fun x => f (t * x)) ∈ boundedFunctions := by
  obtain ⟨b, hb, h⟩ := hf
  exact ⟨b, hb, fun x => h (t * x)⟩

/-- Every character component of a bounded finite sum of distinct characters
is bounded separately. -/
theorem bounded_character_component {ι : Type w}
    (χ : ι → H →* K) (hχ : Function.Injective χ)
    (s : Finset ι) (c : ι → K)
    (hs : (∑ i ∈ s, c i • (χ i : H → K)) ∈ boundedFunctions) :
    ∀ i ∈ s, c i • (χ i : H → K) ∈ boundedFunctions :=
  character_component_mem boundedFunctions boundedFunctions_translate χ hχ s c hs

end BoundedFunctions

end Langlands.GroupScheme.BoundedCharacterComponents
