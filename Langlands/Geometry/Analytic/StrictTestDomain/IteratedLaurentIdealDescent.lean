import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentIdealDescent
import Langlands.Geometry.Analytic.StrictTestDomain.LaurentSplitIdealDescent
import Langlands.Geometry.Analytic.StrictTestDomain.IdealCoverRefinement
import Langlands.Geometry.Analytic.StrictTestDomain.AllUnitLaurentRefinement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalPresheaf

/-! # Closed-ideal descent for finite iterated Laurent covers and all-unit standard covers -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace RationalData

variable {P : PresentedStrictAffinoidAlgebra K} {m : ℕ}

/-- Over the quotient of a first binary branch, the leaf of the mapped tail
tuple is included in the pulled-back full leaf with that first choice. -/
def iteratedLaurentBranchInclusion (g : Fin (m + 1) → P) (b : Bool) (η : Fin m → Bool) :
    iteratedLaurent (fun i : Fin m => (laurentChoice (g 0) b).baseMap (g i.succ)) η ⟶
      (iteratedLaurent g (Fin.cons b η)).pullback (laurentChoice (g 0) b).baseMap :=
  (iteratedLaurentBranchIso g (Fin.cons b η)).inv

end RationalData

/-- The actual strict binary Laurent cover has ideal descent in existence form. -/
theorem binaryIdealDescent_laurent (hK : ∃ c : K, 1 < ‖c‖)
    {P : PresentedStrictAffinoidAlgebra K} (f : P) :
    BinaryIdealDescent (laurentUpper f) (laurentLower f) := fun I J h =>
  ⟨_, laurent_closedIdealMap_inf_comap_eq hK f I J h⟩

private theorem idealCoverDescent_iteratedLaurent_zero (hK : ∃ c : K, 1 < ‖c‖)
    (P : PresentedStrictAffinoidAlgebra K) (g : Fin 0 → P) :
    IdealCoverDescent (fun ε : Fin 0 → Bool => iteratedLaurent g ε) := by
  intro I _ ε
  apply le_antisymm
  · apply ((iteratedLaurent g ε).baseMap.closedIdealMap_le_iff _ _
      (PresentedStrictAffinoidAlgebra.isClosed_ideal hK _ (I ε))).mpr
    intro a ha
    exact (mem_idealSectionContraction _ I a).mp ha ε
  · intro s hs
    have hs' : (whole K P).baseMap (wholeEvaluation K P s) = s :=
      congrArg (fun φ => φ s) (wholeBaseMap_comp_evaluation K P)
    rw [← hs']
    apply (iteratedLaurent g ε).baseMap.mem_closedIdealMap
    rw [mem_idealSectionContraction]
    intro η
    obtain rfl : η = ε := Subsingleton.elim _ _
    change (whole K P).baseMap (wholeEvaluation K P s) ∈ I η
    rw [hs']
    exact hs

/-- Closed-ideal descent for every finite iterated unit-radius Laurent cover
of a presented strict affinoid algebra over a nontrivially normed field. -/
theorem idealCoverDescent_iteratedLaurent (hK : ∃ c : K, 1 < ‖c‖) (m : ℕ) :
    ∀ (P : PresentedStrictAffinoidAlgebra K) (g : Fin m → P),
      IdealCoverDescent (fun ε : Fin m → Bool => iteratedLaurent g ε) := by
  induction m with
  | zero => exact idealCoverDescent_iteratedLaurent_zero hK
  | succ m ih =>
      intro P g
      have hbranch : ∀ b : Bool, IdealCoverDescent
          (fun ε : Fin (m + 1) → Bool =>
            (iteratedLaurent g ε).pullback (laurentChoice (g 0) b).baseMap) := fun b =>
        IdealCoverDescent.of_refinement hK _
          (fun η : Fin m → Bool =>
            iteratedLaurent (fun i : Fin m => (laurentChoice (g 0) b).baseMap (g i.succ)) η)
          (iteratedLaurent_covers _) (fun η => Fin.cons b η)
          (iteratedLaurentBranchInclusion g b) (ih _ _)
      exact laurentSplitIdealDescent hK (fun ε => iteratedLaurent g ε)
        (iteratedLaurent_covers g) (g 0) (binaryIdealDescent_laurent hK (g 0))
        (hbranch false) (hbranch true)

/-- Closed-ideal descent for the standard rational cover of a finite tuple of
units without common spectrum zero. -/
theorem idealCoverDescent_allUnitStandardRational (hK : ∃ c : K, 1 < ‖c‖)
    {P : PresentedStrictAffinoidAlgebra K} {n : ℕ} (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0) (hu : ∀ j, IsUnit (f j)) :
    IdealCoverDescent (standardRational f hf) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro _ _ i
    exact Fin.elim0 i
  · exact IdealCoverDescent.of_refinement hK (standardRational f hf)
      (fun ε : Fin (n * n) → Bool => iteratedLaurent (allUnitRatios f) ε)
      (iteratedLaurent_covers _) (fun ε => allUnitLaurentIndex ⟨ε, hn⟩)
      (fun ε => allUnitLaurentInclusion f hf hu ⟨ε, hn⟩)
      (idealCoverDescent_iteratedLaurent hK (n * n) P (allUnitRatios f))

end Langlands.Analytic.StrictTestDomain
