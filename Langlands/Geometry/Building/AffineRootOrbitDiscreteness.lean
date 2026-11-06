import Langlands.Geometry.Building.AffineReflectionGalleryGeometryStatement
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Discreteness of orbits of root-permuting affine automorphisms

For a locally finite affine reflection arrangement `Ψ` on a finite-dimensional
real normed affine space, every orbit of the group of affine automorphisms
permuting `Ψ` is discrete. This is the apartment step in the proof of KP
Lemma 4.2.11.
-/

noncomputable section

open Filter Topology Set

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- Orbit discreteness at a point: an affine automorphism permuting `Ψ` which
moves `a` by less than `ε` fixes `a`. The values at `e a` of finitely many roots
whose derivatives span `V*` lie in a finite set of values at `a`. -/
theorem exists_forall_dist_lt_imp_eq {Ψ : Set (P →ᵃ[ℝ] ℝ)}
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ) (a : P) :
    ∃ ε > 0, ∀ e ∈ rootStabilizer Ψ, dist (e a) a < ε → e a = a := by
  have hrep : ∀ φ : derivativeRoots Ψ, ∃ ψ ∈ Ψ, ψ.linear = (φ : Module.Dual ℝ V) :=
    fun φ => φ.2
  choose rep hrepΨ hrepLin using hrep
  have := hΨ.finite_derivativeRoots.to_subtype
  obtain ⟨C, hC⟩ := (Set.finite_range fun φ : derivativeRoots Ψ => |rep φ a|).bddAbove
  set S := {ψ | ψ ∈ Ψ ∧ |ψ a| ≤ C}
  have hS : S.Finite := hΨ.finite_bounded_at a fun _ => C
  set T := (fun ψ : P →ᵃ[ℝ] ℝ => ψ a) '' {ψ | ψ ∈ Ψ ∧ |ψ a| ≤ C + 1}
  have hT : T.Finite := (hΨ.finite_bounded_at a fun _ => C + 1).image _
  have hnear : ∀ ψ ∈ S, ∀ᶠ x in 𝓝 a, |ψ x - ψ a| < 1 ∧ ∀ t ∈ T, t ≠ ψ a → ψ x ≠ t := by
    intro ψ _
    have hψ := ψ.continuous_of_finiteDimensional.tendsto a
    refine (hψ.eventually (Metric.ball_mem_nhds (ψ a) one_pos)).and
      (hT.eventually_all.2 fun t _ => ?_) |>.mono fun x hx => ⟨?_, hx.2⟩
    · by_cases ht : t = ψ a
      · exact Eventually.of_forall fun _ h => absurd ht h
      · exact (hψ.eventually (eventually_ne_nhds (Ne.symm ht))).mono fun _ hx _ => hx
    · simpa [Real.dist_eq] using hx.1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hS.eventually_all.2 hnear)
  refine ⟨ε, hε, fun e he hea => ?_⟩
  have hval : ∀ ψ ∈ S, ψ (e a) = ψ a := by
    intro ψ hψS
    obtain ⟨h1, h2⟩ := hball hea ψ hψS
    have hη : ψ.comp (e : P →ᵃ[ℝ] P) ∈ Ψ := (he ψ).2 hψS.1
    have hηa : (ψ.comp (e : P →ᵃ[ℝ] P)) a = ψ (e a) := rfl
    have hbound : |ψ (e a)| ≤ C + 1 := by
      calc |ψ (e a)| = |ψ a + (ψ (e a) - ψ a)| := by ring_nf
        _ ≤ |ψ a| + |ψ (e a) - ψ a| := abs_add_le _ _
        _ ≤ C + 1 := add_le_add hψS.2 h1.le
    by_contra hne
    exact h2 (ψ (e a)) ⟨_, ⟨hη, hηa ▸ hbound⟩, hηa⟩ hne rfl
  have hzero : ∀ φ ∈ derivativeRoots Ψ, φ (e a -ᵥ a) = 0 := by
    intro φ hφ
    have hmem : rep ⟨φ, hφ⟩ ∈ S := ⟨hrepΨ _, hC ⟨⟨φ, hφ⟩, rfl⟩⟩
    have hlin : (rep ⟨φ, hφ⟩).linear = φ := hrepLin ⟨φ, hφ⟩
    rw [← hlin, AffineMap.linearMap_vsub, hval _ hmem, vsub_self]
  have hspan : Submodule.span ℝ (derivativeRoots Ψ) ≤
      LinearMap.ker (Module.Dual.eval ℝ V (e a -ᵥ a)) :=
    Submodule.span_le.2 fun φ hφ => hzero φ hφ
  rw [hΨ.span_derivativeRoots_eq_top, top_le_iff] at hspan
  have hv : e a -ᵥ a = 0 :=
    (Module.forall_dual_apply_eq_zero_iff ℝ (e a -ᵥ a)).1 fun φ => by
      have : φ ∈ LinearMap.ker (Module.Dual.eval ℝ V (e a -ᵥ a)) := hspan ▸ Submodule.mem_top
      exact this
  exact vsub_eq_zero_iff_eq.1 hv

end Langlands.Geometry.Building.AffineRootSystem
