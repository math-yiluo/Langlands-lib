import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Rational.IndependentStandardCocharacter
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Codimension of independent-character annihilators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Simultaneous evaluation of selected actual characters on real cocharacters. -/
def rootEvaluation (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (J : Set (characterLattice T)) : V T →ₗ[ℝ] (J → ℝ) :=
  LinearMap.pi fun α => eval T α.1

@[simp] theorem rootEvaluation_apply (J : Set (characterLattice T))
    (v : V T) (α : J) : rootEvaluation T J v α = eval T α.1 v := rfl

/-- The published annihilator is the kernel of simultaneous evaluation. -/
theorem ker_rootEvaluation (J : Set (characterLattice T)) :
    (rootEvaluation T J).ker = rootAnnihilator T J := by
  ext v
  simp only [LinearMap.mem_ker, funext_iff, rootEvaluation_apply, Pi.zero_apply,
    mem_rootAnnihilator]
  exact SetCoe.forall

/-- Independent rationalized characters have arbitrary prescribed real
evaluations on real cocharacters of a split torus. -/
theorem rootEvaluation_surjective (hT : IsSplitTorus T.toGrp)
    (J : Set (characterLattice T)) [Finite J]
    (hJ : LinearIndependent ℚ (fun α : J => toRat (α : characterLattice T))) :
    Function.Surjective (rootEvaluation T J) := by
  classical
  let := Fintype.ofFinite J
  have hsep (β : J) := hT.exists_scaled_pairings
    (fun α : J => (α : characterLattice T)) hJ
    (fun α => if α = β then 1 else 0)
  choose d hd z hz using hsep
  have hdne (β : J) : (d β : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hd β))
  have hpair (α β : J) :
      (latticePairing T α.1 (z β) : ℝ) =
        (d β : ℝ) * (if α = β then 1 else 0) := by
    exact_mod_cast hz β α
  intro x
  refine ⟨∑ β : J, (x β / (d β : ℝ)) ⊗ₜ[ℤ] z β, ?_⟩
  ext α
  change eval T α.1 (∑ β : J, (x β / (d β : ℝ)) ⊗ₜ[ℤ] z β) = x α
  simp [map_sum, eval_tmul, hpair, hdne]

/-- Rank-nullity for the common annihilator of independent rationalized
characters of a split torus, including the empty selection. -/
theorem finrank_rootAnnihilator_add_card (hT : IsSplitTorus T.toGrp)
    [Module.Finite ℝ (V T)] (J : Set (characterLattice T)) [Finite J]
    (hJ : LinearIndependent ℚ (fun α : J => toRat (α : characterLattice T))) :
    Module.finrank ℝ (rootAnnihilator T J) + Nat.card J =
      Module.finrank ℝ (V T) := by
  let := Fintype.ofFinite J
  have h := (rootEvaluation T J).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (rootEvaluation_surjective hT J hJ),
    ker_rootEvaluation, finrank_top] at h
  simpa [Module.finrank_pi, Nat.card_eq_fintype_card, Nat.add_comm] using h

end Langlands.GroupScheme.RealTorusSpace
