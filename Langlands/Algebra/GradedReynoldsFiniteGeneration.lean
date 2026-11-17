import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Finite generation from a Reynolds projection -/

namespace Langlands.Algebra

universe u v

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]

/-- A linear retraction onto a subalgebra that commutes with multiplication by its
elements. No group action or grading is part of this data. -/
structure SubalgebraReynoldsProjection (S : Subalgebra k A) where
  map : A →ₗ[k] A
  mem : ∀ a, map a ∈ S
  fix : ∀ a ∈ S, map a = a
  mul_left : ∀ s ∈ S, ∀ a, map (s * a) = s * map a

/-- A graded subalgebra of a Noetherian algebra with scalar degree zero is finitely
generated if it admits a linear retraction that is linear over the subalgebra.
The retraction need not preserve degrees. -/
theorem subalgebra_fg_of_graded_reynolds [IsNoetherianRing A]
    (S : Subalgebra k A) (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (P : A →ₗ[k] A)
    (hPmem : ∀ a, P a ∈ S)
    (hPfix : ∀ a ∈ S, P a = a)
    (hPmul : ∀ s ∈ S, ∀ a, P (s * a) = s * P a)
    (hS : ∀ d a, a ∈ S → GradedRing.proj 𝒜 d a ∈ S)
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a) :
    S.FG := by
  classical
  set H : Set A := {a | a ∈ S ∧ ∃ d, 0 < d ∧ a ∈ 𝒜 d}
  obtain ⟨T, hTH, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset H).1
    (IsNoetherian.noetherian (Submodule.span A H))
  choose! e he using fun t (ht : t ∈ T) => (hTH ht).2
  have key : ∀ d, ∀ a ∈ 𝒜 d, a ∈ S → a ∈ Algebra.adjoin k (T : Set A) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro a ha haS
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · obtain ⟨c, rfl⟩ := h0 a ha
        exact Subalgebra.algebraMap_mem _ c
      · have haH : a ∈ Submodule.span A (T : Set A) :=
          hT ▸ Submodule.subset_span ⟨haS, d, hd, ha⟩
        obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 haH
        have haP : a = ∑ t ∈ T, P (f t) * t := by
          calc
            a = P a := (hPfix a haS).symm
            _ = ∑ t ∈ T, P (f t * t) := by rw [← hf, map_sum]; rfl
            _ = _ := by
              refine Finset.sum_congr rfl fun t ht => ?_
              rw [mul_comm (f t), hPmul t (hTH ht).1, mul_comm t]
        have hsum : a = ∑ t ∈ T,
            (if e t ≤ d then GradedRing.proj 𝒜 (d - e t) (P (f t)) * t else 0) := by
          calc
            a = GradedRing.proj 𝒜 d a := by
              rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha]
            _ = ∑ t ∈ T, GradedRing.proj 𝒜 d (P (f t) * t) := by
              rw [haP, map_sum]
            _ = _ := by
              refine Finset.sum_congr rfl fun t ht => ?_
              rw [GradedRing.proj_apply,
                DirectSum.coe_decompose_mul_of_right_mem 𝒜 d (he t ht).2]
              split_ifs <;> rfl
        rw [hsum]
        refine Subalgebra.sum_mem _ fun t ht => ?_
        split_ifs with hle
        · refine Subalgebra.mul_mem _ (ih (d - e t) (by have := (he t ht).1; omega)
            _ ?_ ?_) (Algebra.subset_adjoin ht)
          · rw [GradedRing.proj_apply]
            exact (DirectSum.decompose 𝒜 (P (f t)) (d - e t)).2
          · exact hS _ _ (hPmem _)
        · exact Subalgebra.zero_mem _
  refine ⟨T, le_antisymm ?_ fun a ha => ?_⟩
  · exact Algebra.adjoin_le fun t ht => (hTH ht).1
  · rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine Subalgebra.sum_mem _ fun d _ => key d _ (DirectSum.decompose 𝒜 a d).2 ?_
    simpa [GradedRing.proj_apply] using hS d a ha

/-- The finite-generation theorem applied to a packaged Reynolds projection. -/
theorem SubalgebraReynoldsProjection.fg [IsNoetherianRing A]
    {S : Subalgebra k A} (P : SubalgebraReynoldsProjection S)
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (hS : ∀ d a, a ∈ S → GradedRing.proj 𝒜 d a ∈ S)
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a) : S.FG :=
  subalgebra_fg_of_graded_reynolds S 𝒜 P.map P.mem P.fix P.mul_left hS h0

end Langlands.Algebra
