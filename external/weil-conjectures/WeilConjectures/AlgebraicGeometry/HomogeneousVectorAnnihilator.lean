/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# HomogeneousVectorAnnihilator

Source: Stacks Project, Constructions, Section 01M3, stalk computation before
Definition 01M6 (blueprint: lem-weil-pbc-homogeneous-vector-annihilator).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- A homogeneous vector killed by a scalar outside a homogeneous prime is killed by
one homogeneous scalar outside that prime.
Source: Stacks Project, Constructions, Section 01M3, stalk computation before
Definition 01M6; the homogeneous-component argument underlying injectivity.
(blueprint: lem-weil-pbc-homogeneous-vector-annihilator)

Proof:
Decompose c into its finitely many homogeneous components c_k. Since the prime is
homogeneous and c is outside it, some c_k is outside it. The sum of c_k • y equals
c • y = 0. Each summand is in the graded piece of degree k+z. These degrees are
pairwise distinct because addition by z in the integers is injective. Internality
of the module grading therefore forces each summand to vanish. Take b=c_k.
For y=0 any component outside the prime works; negative z and degree-zero b require
no modification. There is no assumption that the ring or the module is a domain.
-/
theorem homogeneousVectorAnnihilator
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (x : Proj 𝒜) (z : ℤ) (y : M) (hy : y ∈ 𝓜 z)
    (c : S) (hc : c ∉ x.asHomogeneousIdeal) (hcy : c • y = 0) :
    ∃ (k : ℕ) (b : S), b ∈ 𝒜 k ∧ b ∉ x.asHomogeneousIdeal ∧ b • y = 0  := by
  classical
  let := h𝓜.chooseDecomposition
  have hc' : ¬ ∀ k, (DirectSum.decompose 𝒜 c k : S) ∈ x.asHomogeneousIdeal.toIdeal := by
    intro h
    exact hc ((Ideal.IsHomogeneous.mem_iff 𝒜 x.asHomogeneousIdeal.is_homogeneous').mpr h)
  obtain ⟨k, hk⟩ := not_forall.mp hc'
  have hks : k ∈ (DirectSum.decompose 𝒜 c).support := by
    by_contra hks
    have hz := DFinsupp.notMem_support_iff.mp hks
    apply hk
    rw [hz]
    exact x.asHomogeneousIdeal.toIdeal.zero_mem
  have hcomp : (DirectSum.decompose 𝓜 (c • y) ((k : ℤ) + z) : M) =
      (DirectSum.decompose 𝒜 c k : S) • y := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 c, Finset.sum_smul,
      DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
    rw [Finset.sum_eq_single_of_mem k hks]
    · exact DirectSum.decompose_of_mem_same 𝓜
        (hsmul k z _ y (DirectSum.decompose 𝒜 c k).prop hy)
    · intro j _ hj
      exact DirectSum.decompose_of_mem_ne 𝓜
        (hsmul j z _ y (DirectSum.decompose 𝒜 c j).prop hy)
        (by intro heq; exact hj (Int.natCast_inj.mp (add_right_cancel heq)))
  refine ⟨k, DirectSum.decompose 𝒜 c k, (DirectSum.decompose 𝒜 c k).prop, hk, ?_⟩
  rw [← hcomp, hcy, DirectSum.decompose_zero]
  rfl

end AlgebraicGeometry.Proj
