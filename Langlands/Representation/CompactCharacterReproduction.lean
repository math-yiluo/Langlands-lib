import Langlands.Representation.CompactSchurAveragingProof

/-! # Inverse-character reproduction on the irreducible source model -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Representation.CompactSchur

open MeasureTheory
open scoped BigOperators

variable {d : ℕ}

/-- A coordinate rank-one endomorphism with prescribed image vector. -/
def rankOne (j : Fin d) (v : Fin d → ℂ) : Module.End ℂ (Fin d → ℂ) :=
  (LinearMap.proj j : (Fin d → ℂ) →ₗ[ℂ] ℂ).smulRight v

@[simp]
theorem rankOne_apply (j : Fin d) (v w : Fin d → ℂ) :
    rankOne j v w = w j • v := rfl

@[simp]
theorem trace_rankOne (j : Fin d) (v : Fin d → ℂ) :
    Matrix.trace (LinearMap.toMatrix' (rankOne j v)) = v j := by
  classical
  simp [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix'_apply,
    Pi.single_apply, smul_eq_mul]

variable {G : Type u} [Group G]

theorem sum_rankOne_conjugate
    (ρ : _root_.Representation ℂ G (Fin d → ℂ)) (v : Fin d → ℂ) (k : G) :
    (∑ j : Fin d, ρ k (rankOne j v (ρ k⁻¹ (Pi.single j 1)))) =
      Matrix.trace (LinearMap.toMatrix' (ρ k⁻¹)) • ρ k v := by
  simp only [rankOne_apply, map_smul]
  rw [← Finset.sum_smul]
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem inverseCharacter_integrable
    (ρ : _root_.Representation ℂ G (Fin d → ℂ))
    (hρ : Continuous (fun p : G × (Fin d → ℂ) => ρ p.1 p.2))
    (ν : Measure G) [IsFiniteMeasure ν] (v : Fin d → ℂ) :
    Integrable (fun k : G =>
      Matrix.trace (LinearMap.toMatrix' (ρ k⁻¹)) • ρ k v) ν := by
  have hi := integrable_finsetSum Finset.univ
    (fun (j : Fin d) _ => integrable_conjugate ρ hρ ν (rankOne j v) (Pi.single j 1))
  simpa only [sum_rankOne_conjugate] using hi

/-- The dimension times inverse character reproduces every vector of the source. -/
theorem inverseCharacter_reproduces
    (ρ : _root_.Representation ℂ G (Fin d → ℂ))
    (hρ : Continuous (fun p : G × (Fin d → ℂ) => ρ p.1 p.2))
    (hirr : ρ.IsIrreducible)
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (v : Fin d → ℂ) :
    (d : ℂ) • (∫ k : G,
      Matrix.trace (LinearMap.toMatrix' (ρ k⁻¹)) • ρ k v ∂ν) = v := by
  classical
  have hs (j : Fin d) :
      (d : ℂ) • (∫ k : G,
        ρ k (rankOne j v (ρ k⁻¹ (Pi.single j 1))) ∂ν) =
          v j • Pi.single j 1 := by
    simpa only [trace_rankOne] using
      compactSchurAveraging G d ρ hρ hirr ν (rankOne j v) (Pi.single j 1)
  calc
    (d : ℂ) • (∫ k : G,
        Matrix.trace (LinearMap.toMatrix' (ρ k⁻¹)) • ρ k v ∂ν) =
      (d : ℂ) • (∫ k : G,
        ∑ j : Fin d, ρ k (rankOne j v (ρ k⁻¹ (Pi.single j 1))) ∂ν) := by
      congr 2
      funext k
      exact (sum_rankOne_conjugate ρ v k).symm
    _ = ∑ j : Fin d, (d : ℂ) • (∫ k : G,
        ρ k (rankOne j v (ρ k⁻¹ (Pi.single j 1))) ∂ν) := by
      rw [integral_finsetSum Finset.univ
        (fun j _ => integrable_conjugate ρ hρ ν (rankOne j v) (Pi.single j 1)),
        Finset.smul_sum]
    _ = ∑ j : Fin d, v j • Pi.single j 1 := by
      exact Finset.sum_congr rfl (fun j _ => hs j)
    _ = v := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]

end Langlands.Representation.CompactSchur
