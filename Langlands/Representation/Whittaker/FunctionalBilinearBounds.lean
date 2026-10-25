import Langlands.Representation.Whittaker.FunctionalLength
import Langlands.Representation.Filtration.InvariantBilinearBounds

/-! Finite exceptional sets and bilinear bounds from unique functional factors. -/

noncomputable section

namespace Langlands.InvariantBilinear

universe uZ uS uG uV uW

/-- The union of the exceptional sets at every pair of actual graded positions. -/
def gradedExceptionSet {Z : Type uZ} {m n : ℕ}
    (E : Fin m → Fin n → Finset Z) : Finset Z := by
  classical
  exact Finset.univ.biUnion fun i => Finset.univ.biUnion (E i)

theorem mem_gradedExceptionSet {Z : Type uZ} {m n : ℕ}
    (E : Fin m → Fin n → Finset Z) (z : Z) :
    z ∈ gradedExceptionSet E ↔ ∃ i j, z ∈ E i j := by
  classical
  simp [gradedExceptionSet]

theorem not_mem_pair_of_not_mem_gradedExceptionSet {Z : Type uZ} {m n : ℕ}
    (E : Fin m → Fin n → Finset Z) {z : Z}
    (hz : z ∉ gradedExceptionSet E) (i : Fin m) (j : Fin n) :
    z ∉ E i j :=
  fun h => hz ((mem_gradedExceptionSet E z).mpr ⟨i, j, h⟩)

section FunctionalFactors

variable {G : Type uG} [Group G]
variable {A : Rep.{uV} ℂ G} {B : Rep.{uW} ℂ G} {m n : ℕ}
variable (U U' : Subgroup G) (θ : U →* ℂˣ) (θ' : U' →* ℂˣ)
variable (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)

/-- Unique functional positions reduce a pairwise rigidity bound to total length one. -/
theorem length_le_one_of_unique_functional_factors (χ : G → ℂ)
    (hA : ∃! i : Fin m,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ)
    (hB : ∃! j : Fin n,
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ)
    (hdetect : ∀ i j,
      length (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ χ ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ)
    (hbound : ∀ i j,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
      length (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ χ ≤ 1) :
    length A.ρ B.ρ χ ≤ 1 := by
  classical
  obtain ⟨i₀, hi₀, hi⟩ := hA
  obtain ⟨j₀, hj₀, hj⟩ := hB
  apply (length_le_of_single_pair f g χ i₀ j₀ ?_).trans (hbound i₀ j₀ hi₀ hj₀)
  intro i j hij
  by_contra hne
  obtain ⟨hfi, hgj⟩ := hdetect i j hne
  exact hij.elim (fun h => h (hi i hfi)) (fun h => h (hj j hgj))

/-- Choose one finite exceptional set before the spectral parameter or any form. -/
theorem exists_exception_length_le_one_of_unique_functional_factors
    {Z : Type uZ} {S : Type uS} (z : S → Z) (χ : S → G → ℂ)
    (hA : ∃! i : Fin m,
      Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ)
    (hB : ∃! j : Fin n,
      Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ)
    (hpair : ∀ i j, ∃ E : Finset Z, ∀ a : S, z a ∉ E →
      (length (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ (χ a) ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) ∧
      (Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
        length (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ (χ a) ≤ 1)) :
    ∃ E : Finset Z, ∀ a : S, z a ∉ E → length A.ρ B.ρ (χ a) ≤ 1 := by
  classical
  choose E hE using hpair
  refine ⟨gradedExceptionSet E, ?_⟩
  intro a ha
  have hp := fun i j => hE i j a
    (not_mem_pair_of_not_mem_gradedExceptionSet E ha i j)
  exact length_le_one_of_unique_functional_factors U U' θ θ' f g (χ a) hA hB
    (fun i j => (hp i j).1) (fun i j => (hp i j).2)

end FunctionalFactors

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Rep.{uV} ℂ G} {B : Rep.{uW} ℂ G} {m n : ℕ}
variable (U U' : Subgroup G)
variable (hU : Jacquet.Localization.IsLimitOfCompactSubgroups U)
variable (hU' : Jacquet.Localization.IsLimitOfCompactSubgroups U')
variable (θ : U →* ℂˣ) (θ' : U' →* ℂˣ)
variable (hθ : IsLocallyConstant (fun u : U => (θ u : ℂ)))
variable (hθ' : IsLocallyConstant (fun u : U' => (θ' u : ℂ)))
variable (f : ObjectRepFiltration A m) (g : ObjectRepFiltration B n)

include hU hU' hθ hθ'

/-- Actual smooth functional exactness supplies the unique positions needed above. -/
theorem exists_exception_length_le_one_of_functional_equiv
    {Z : Type uZ} {S : Type uS} (z : S → Z) (χ : S → G → ℂ)
    (hA : IsSmooth A.ρ) (hB : IsSmooth B.ρ)
    (eA : Whittaker.functionals U θ A.ρ ≃ₗ[ℂ] ℂ)
    (eB : Whittaker.functionals U' θ' B.ρ ≃ₗ[ℂ] ℂ)
    (hpair : ∀ i j, ∃ E : Finset Z, ∀ a : S, z a ∉ E →
      (length (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ (χ a) ≠ 0 →
        Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ ∧
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ) ∧
      (Whittaker.HasFunctional (N := U) (θ := θ) (f.gradedRepresentation i).ρ →
        Whittaker.HasFunctional (N := U') (θ := θ') (g.gradedRepresentation j).ρ →
        length (f.gradedRepresentation i).ρ (g.gradedRepresentation j).ρ (χ a) ≤ 1)) :
    ∃ E : Finset Z, ∀ a : S, z a ∉ E → length A.ρ B.ρ (χ a) ≤ 1 :=
  exists_exception_length_le_one_of_unique_functional_factors U U' θ θ' f g z χ
    (Whittaker.existsUnique_hasFunctional_factor U hU θ hθ f hA eA)
    (Whittaker.existsUnique_hasFunctional_factor U' hU' θ' hθ' g hB eB) hpair

end Smooth

end Langlands.InvariantBilinear
