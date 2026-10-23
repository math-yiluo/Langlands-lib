import Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Fixed lines over commutative compact-open Hecke corners -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure

universe uG uV uW

/-- A finite-dimensional nonzero complex space carrying a transitive set of pairwise
commuting endomorphisms is a line: each endomorphism is a scalar on an eigenvector, hence
everywhere, and transitivity then makes one nonzero vector span. -/
theorem finrank_eq_one_of_commute_of_transitive {W : Type uW} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Nontrivial W] (S : Set (Module.End ℂ W))
    (hS : ∀ T ∈ S, ∀ T' ∈ S, T * T' = T' * T)
    (htr : ∀ w : W, w ≠ 0 → ∀ v : W, ∃ T ∈ S, T w = v) :
    Module.finrank ℂ W = 1 := by
  have hscalar : ∀ T ∈ S, ∃ c : ℂ, ∀ v : W, T v = c • v := by
    intro T hT
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
    refine ⟨c, fun v => ?_⟩
    obtain ⟨T', hT', rfl⟩ := htr u (Module.End.hasEigenvector_iff.mp hu).2 v
    rw [← Module.End.mul_apply, hS T hT T' hT', Module.End.mul_apply, hu.apply_eq_smul,
      map_smul]
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  rw [finrank_eq_one_iff_of_nonzero' w hw]
  intro v
  obtain ⟨T, hT, rfl⟩ := htr w hw v
  obtain ⟨c, hc⟩ := hscalar T hT
  exact ⟨c, (hc w).symm⟩

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (N : OpenSubgroup G) (hN : IsCompact (N : Set G))

include hρ in
/-- If the compact-open corner `H_N` is commutative, the nonzero `N`-fixed space of an
irreducible smooth representation with finite-dimensional `N`-fixed space is a line. -/
theorem finrank_fixedVectors_eq_one_of_corner_comm
    (hcomm : ∀ f g : HeckeAlgebra.Corner μ N hN, f * g = g * f)
    (hirr : ρ.IsIrreducible) (hfin : Module.Finite ℂ (fixedVectors ρ N.toSubgroup))
    (h0 : fixedVectors ρ N.toSubgroup ≠ ⊥) :
    Module.finrank ℂ (fixedVectors ρ N.toSubgroup) = 1 := by
  have hsimple := CompactCoefficientClass.isSimpleModule_fixedVectors μ ρ hρ N hN hirr h0
  let _ := cornerModule μ ρ hρ N hN
  rw [isSimpleModule_iff_toSpanSingleton_surjective] at hsimple
  obtain ⟨hnt, hsurj⟩ := hsimple
  refine finrank_eq_one_of_commute_of_transitive (Set.range (cornerAction μ ρ hρ N hN)) ?_ ?_
  · rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
    rw [← map_mul, hcomm, map_mul]
  · intro w hw v
    obtain ⟨f, hf⟩ := hsurj w hw v
    exact ⟨cornerAction μ ρ hρ N hN f, ⟨f, rfl⟩, hf⟩

end Langlands.Hecke
