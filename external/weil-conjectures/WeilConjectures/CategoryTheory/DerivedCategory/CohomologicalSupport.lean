/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!

# The cohomological support of an object of a derived category

For an abelian category `C` and `K : D(C)`, the *cohomological support* of `K` is the set of
degrees `r ∈ ℤ` in which the cohomology object `Hʳ(K)` does not vanish (blueprint
`def-weil-cohomological-support`). For the small pro-étale site `C = Sh(Y_proét, Λ)` the
cohomology objects are the cohomology sheaves `ℋʳ(K)` of the blueprint.

## Main definitions

- `DerivedCategory.cohomologicalSupport`: the set `{r ∈ ℤ | Hʳ(K) ≠ 0}`.

## Main statements

- `DerivedCategory.cohomologicalSupport_subset_Icc_iff`: the support lies in `[a, b]` exactly
  when `K` has homology concentrated in `[a, b]`.
- `DerivedCategory.bounded_iff_exists_cohomologicalSupport_subset_Icc`: `K` is bounded exactly
  when its support lies in some interval.
- `DerivedCategory.cohomologicalSupport_shift`: shifting by `n` translates the support by `-n`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Blueprint `def-weil-cohomological-support`: Cohomological support.

The *cohomological support* of `K : D(C)` is the set of degrees in which its cohomology does not
vanish: `Supp_coh(K) = {r ∈ ℤ | Hʳ(K) ≠ 0}`. -/
def cohomologicalSupport (K : DerivedCategory C) : Set ℤ :=
  {r | ¬ IsZero ((homologyFunctor C r).obj K)}

lemma mem_cohomologicalSupport_iff (K : DerivedCategory C) (r : ℤ) :
    r ∈ cohomologicalSupport K ↔ ¬ IsZero ((homologyFunctor C r).obj K) :=
  Iff.rfl

lemma not_mem_cohomologicalSupport_iff (K : DerivedCategory C) (r : ℤ) :
    r ∉ cohomologicalSupport K ↔ IsZero ((homologyFunctor C r).obj K) :=
  not_not

/-- Isomorphic objects have the same cohomological support. -/
lemma cohomologicalSupport_eq_of_iso {K L : DerivedCategory C} (e : K ≅ L) :
    cohomologicalSupport K = cohomologicalSupport L := by
  ext r
  simp only [mem_cohomologicalSupport_iff]
  exact not_congr ⟨fun h ↦ h.of_iso ((homologyFunctor C r).mapIso e).symm,
    fun h ↦ h.of_iso ((homologyFunctor C r).mapIso e)⟩

/-- The cohomological support of `K` is contained in `[a, b]` exactly when `K` has homology
concentrated in `[a, b]`. -/
lemma cohomologicalSupport_subset_Icc_iff (K : DerivedCategory C) (a b : ℤ) :
    cohomologicalSupport K ⊆ Set.Icc a b ↔ homologyConcentratedIn a b K := by
  rw [homologyConcentratedIn_iff]
  change _ ↔ K.IsGE a ∧ K.IsLE b
  rw [isGE_iff, isLE_iff]
  constructor
  · intro h
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · by_contra hz
      exact absurd (h hz).1 (not_le.2 hi)
    · by_contra hz
      exact absurd (h hz).2 (not_le.2 hi)
  · rintro ⟨ha, hb⟩ r hr
    refine ⟨?_, ?_⟩
    · by_contra hlt
      exact hr (ha r (not_le.1 hlt))
    · by_contra hlt
      exact hr (hb r (not_le.1 hlt))

/-- An object of `D(C)` is bounded for the canonical t-structure exactly when its cohomological
support is contained in some interval. -/
lemma bounded_iff_exists_cohomologicalSupport_subset_Icc (K : DerivedCategory C) :
    TStructure.t.bounded K ↔ ∃ a b : ℤ, cohomologicalSupport K ⊆ Set.Icc a b := by
  simp only [cohomologicalSupport_subset_Icc_iff]
  exact (exists_homologyConcentratedIn_iff_bounded K).symm

/-- The cohomological support of the zero object is empty. -/
lemma cohomologicalSupport_eq_empty_of_isZero {K : DerivedCategory C} (hK : IsZero K) :
    cohomologicalSupport K = ∅ := by
  ext r
  simp only [mem_cohomologicalSupport_iff, Set.mem_empty_iff_false, iff_false, not_not]
  exact Functor.map_isZero _ hK

/-- Shifting by `n` translates the cohomological support by `-n`:
`Hʳ(K[n]) = H^{r + n}(K)`. -/
lemma cohomologicalSupport_shift (K : DerivedCategory C) (n : ℤ) :
    cohomologicalSupport (K⟦n⟧) = (fun r ↦ r - n) '' cohomologicalSupport K := by
  ext r
  simp only [Set.mem_image, mem_cohomologicalSupport_iff]
  constructor
  · intro h
    refine ⟨r + n, fun h' ↦ h (h'.of_iso ?_), by omega⟩
    exact ((homologyFunctor C 0).shiftIso n r (r + n) (by omega)).app K
  · rintro ⟨s, hs, rfl⟩ h'
    exact hs (h'.of_iso (((homologyFunctor C 0).shiftIso n (s - n) s (by omega)).app K).symm)

end DerivedCategory
