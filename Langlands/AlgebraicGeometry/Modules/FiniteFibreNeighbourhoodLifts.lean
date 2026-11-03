import Langlands.AlgebraicGeometry.Modules.ProperFibrePowerSectionLiftingStatement

/-! # Simultaneous neighbourhood lifts of finitely many fibre sections -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (M : X.Modules) {ι : Type v}

/-- Actual lifts of an indexed family of fibre sections on a single affine
neighbourhood of the base point. -/
structure FibreNeighbourhoodLifts
    (σ : ι → GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj M)) where
  neighbourhood : S.Opens
  point_mem : s ∈ neighbourhood
  isAffine : IsAffineOpen neighbourhood
  sections : ι → Γ(M, f ⁻¹ᵁ neighbourhood)
  restrict_eq : ∀ i, fibreNeighbourhoodSection f s M point_mem (sections i) = σ i

/-- Finitely many individually liftable fibre sections lift on one affine
neighbourhood, by taking an affine refinement of their intersection. -/
lemma nonempty_fibreNeighbourhoodLifts [Finite ι]
    (σ : ι → GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj M))
    (hσ : ∀ i, ∃ (V : S.Opens) (hsV : s ∈ V) (τ : Γ(M, f ⁻¹ᵁ V)),
      fibreNeighbourhoodSection f s M hsV τ = σ i) :
    Nonempty (FibreNeighbourhoodLifts f s M σ) := by
  classical
  choose V hsV τ hτ using hσ
  have hsI : s ∈ (⨅ i, V i) := by
    change s ∈ ((⨅ i, V i : S.Opens) : Set S)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hsV
  obtain ⟨W, hW, hsW, hWI⟩ := exists_isAffineOpen_mem_and_subset hsI
  have hWV (i : ι) : W ≤ V i :=
    le_trans (show W ≤ ⨅ j, V j from hWI) (iInf_le V i)
  refine ⟨⟨W, hsW, hW,
    fun i => M.presheaf.map (homOfLE (f.preimage_mono (hWV i))).op (τ i), ?_⟩⟩
  intro i
  rw [fibreNeighbourhoodSection_restrict f s M (hsV i) hsW (hWV i)]
  exact hτ i

/-- Choose simultaneous actual lifts on a common affine neighbourhood. -/
def finiteFibreNeighbourhoodLifts [Finite ι]
    (σ : ι → GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj M))
    (hσ : ∀ i, ∃ (V : S.Opens) (hsV : s ∈ V) (τ : Γ(M, f ⁻¹ᵁ V)),
      fibreNeighbourhoodSection f s M hsV τ = σ i) :
    FibreNeighbourhoodLifts f s M σ :=
  (nonempty_fibreNeighbourhoodLifts f s M σ hσ).some

/-- The eventual single-section lifting statement gives simultaneous lifting
for every finite family in every sufficiently large degree. -/
lemma ProperFibrePowerSectionLiftingStatement.finite_family
    (h : ProperFibrePowerSectionLiftingStatement.{u})
    (X S : Scheme.{u}) [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (L : LineBundle X) (s : S)
    (hL : ((LineBundle.pullback (f.fiberι s)).obj L).IsAmple) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ {ι : Type v} [Finite ι]
        (σ : ι → GlobalSections ((Scheme.Modules.pullback (f.fiberι s)).obj
          (tensorPow L.obj n))),
        Nonempty (FibreNeighbourhoodLifts f s (tensorPow L.obj n) σ) := by
  obtain ⟨n₀, hn₀⟩ := h X S f L s hL
  refine ⟨n₀, ?_⟩
  intro n hn ι hι σ
  apply nonempty_fibreNeighbourhoodLifts f s (tensorPow L.obj n) σ
  intro i
  obtain ⟨V, hsV, _, τ, hτ⟩ := hn₀ n hn (σ i)
  exact ⟨V, hsV, τ, hτ⟩

end Langlands.AlgebraicGeometry.Modules
