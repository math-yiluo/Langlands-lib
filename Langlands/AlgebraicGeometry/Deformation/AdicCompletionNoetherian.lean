import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-! # Noetherianness of actual adic completions -/

noncomputable section

universe u

open scoped Topology

namespace Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian

open MvPowerSeries.WithPiTopology

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Evaluate finite power series at the canonical images of a generating family
of the completion ideal. The coefficient map is the actual completion map. -/
def evaluation (I : Ideal R) {n : ℕ} (g : Fin n → R)
    (hg : Ideal.span (Set.range g) = I) :
    MvPowerSeries (Fin n) R →+* AdicCompletion I R := by
  let S := AdicCompletion I R
  let J : Ideal S := I.map (algebraMap R S)
  let : WithIdeal S := ⟨J⟩
  let : UniformSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I
    I.fg_of_isNoetherianRing
  have hJ : IsAdic J := rfl
  let : CompleteSpace S := (hJ.isAdicComplete_iff.mp inferInstance).1
  let : T2Space S := (hJ.isAdicComplete_iff.mp inferInstance).2
  let a : Fin n → S := fun i ↦ algebraMap R S (g i)
  have ha : MvPowerSeries.HasEval a := by
    refine ⟨fun i ↦ WithIdeal.isTopologicallyNilpotent_of_mem ?_, ?_⟩
    · apply Ideal.mem_map_of_mem
      rw [← hg]
      exact Submodule.subset_span ⟨i, rfl⟩
    · simp
  exact MvPowerSeries.eval₂Hom (φ := algebraMap R S)
    (continuous_of_discreteTopology) ha

@[simp]
lemma evaluation_C (I : Ideal R) {n : ℕ} (g : Fin n → R)
    (hg : Ideal.span (Set.range g) = I) (r : R) :
    evaluation I g hg (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r := by
  simp [evaluation, MvPowerSeries.coe_eval₂Hom]

@[simp]
lemma evaluation_X (I : Ideal R) {n : ℕ} (g : Fin n → R)
    (hg : Ideal.span (Set.range g) = I) (i : Fin n) :
    evaluation I g hg (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (g i) := by
  simp [evaluation, MvPowerSeries.coe_eval₂Hom]

/-- Finite power-series evaluation at ideal generators is surjective onto
the actual adic completion. -/
theorem evaluation_surjective (I : Ideal R) {n : ℕ} (g : Fin n → R)
    (hg : Ideal.span (Set.range g) = I) : Function.Surjective (evaluation I g hg) := by
  let S := AdicCompletion I R
  let J : Ideal S := I.map (algebraMap R S)
  let : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I
    I.fg_of_isNoetherianRing
  let f : MvPowerSeries (Fin n) R →+* S := evaluation I g hg
  let M : Ideal (MvPowerSeries (Fin n) R) := Ideal.span (Set.range MvPowerSeries.X)
  have hX : f ∘ MvPowerSeries.X = (algebraMap R S) ∘ g := by
    funext i
    exact evaluation_X I g hg i
  have hmap : M.map f = J := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp, hX]
    change Ideal.span (Set.range ((algebraMap R S) ∘ g)) = I.map (algebraMap R S)
    rw [Set.range_comp, ← Ideal.map_span, hg]
  let : IsHausdorff (M.map f) S := by
    rw [hmap]
    infer_instance
  have hf : Function.Surjective ((Ideal.Quotient.mk (M.map f)).comp f) := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I s)
    refine ⟨MvPowerSeries.C r, ?_⟩
    change Ideal.Quotient.mk (M.map f) (f (MvPowerSeries.C r)) =
      Ideal.Quotient.mk (M.map f) s
    rw [hmap]
    apply Ideal.Quotient.eq.mpr
    dsimp only [J]
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I I.fg_of_isNoetherianRing]
    change AdicCompletion.evalOneₐ I (f (MvPowerSeries.C r) - s) = 0
    have hC : f (MvPowerSeries.C r) = algebraMap R S r := evaluation_C I g hg r
    rw [map_sub, hC]
    change AdicCompletion.evalOneₐ I (AdicCompletion.of I R r) -
      AdicCompletion.evalOneₐ I s = 0
    rw [AdicCompletion.evalOneₐ_of, hr, sub_self]
  exact surjective_of_mk_map_comp_surjective (I := M) f hf

/-- Noetherianness for the actual adic-completion ring, available to typeclass inference. -/
instance instIsNoetherianRing (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) :=
  AdicCompletion.isNoetherianRing_of_isNoetherianRing I

end Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian
