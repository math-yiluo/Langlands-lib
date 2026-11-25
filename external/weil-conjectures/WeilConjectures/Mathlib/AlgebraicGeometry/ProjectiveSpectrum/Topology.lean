/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Relevance of the points of the projective spectrum

Every point of `ProjectiveSpectrum 𝒜` is a relevant homogeneous prime ideal, so it misses some
homogeneous element of positive degree (`ProjectiveSpectrum.exists_homogeneous_notMem`), and
hence homogeneous elements of arbitrarily large degree
(`ProjectiveSpectrum.exists_homogeneous_notMem_of_le`).

## TODO

When upstreaming, the `local_affine` field of `AlgebraicGeometry.Proj` in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean` repeats the proof of
`ProjectiveSpectrum.exists_homogeneous_notMem` inline and should use it instead.
-/

@[expose] public section

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace ProjectiveSpectrum

/-- Every point of `ProjectiveSpectrum 𝒜` is a relevant homogeneous prime ideal, hence misses
some homogeneous element of positive degree. -/
theorem exists_homogeneous_notMem (x : ProjectiveSpectrum 𝒜) :
    ∃ m > 0, ∃ f ∈ 𝒜 m, f ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! h
  refine x.not_irrelevant_le fun z hz ↦ ?_
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  exact x.1.toIdeal.sum_mem fun k hk ↦
    h k (Nat.pos_of_ne_zero <| by aesop) _ (SetLike.coe_mem _)

/-- Every point of `ProjectiveSpectrum 𝒜` misses homogeneous elements of arbitrarily large
degree. -/
theorem exists_homogeneous_notMem_of_le (x : ProjectiveSpectrum 𝒜) (n : ℕ) :
    ∃ m ≥ n, ∃ f ∈ 𝒜 m, f ∉ x.asHomogeneousIdeal := by
  obtain ⟨d, hd, f, hf, hfx⟩ := x.exists_homogeneous_notMem
  refine ⟨n * d, Nat.le_mul_of_pos_right n hd, f ^ n,
    (by simpa [mul_comm] using SetLike.pow_mem_graded n hf),
    fun h ↦ hfx (x.isPrime.mem_of_pow_mem _ h)⟩

/-- **Graded prime avoidance.** For finitely many points of `ProjectiveSpectrum 𝒜` there is a
homogeneous element of positive degree lying in none of them (Stacks, Tag 00JS). -/
theorem exists_homogeneous_notMem_of_finset (s : Finset (ProjectiveSpectrum 𝒜)) :
    ∃ m > 0, ∃ f ∈ 𝒜 m, ∀ x ∈ s, f ∉ x.asHomogeneousIdeal := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, one_pos, 0, zero_mem _, by simp⟩
  obtain ⟨p, hp⟩ := s.exists_minimal hs
  obtain ⟨d, hd, g, hg, hgs⟩ := ih (s.erase p) (Finset.erase_ssubset hp.prop)
  by_cases hgp : g ∉ p.asHomogeneousIdeal
  · refine ⟨d, hd, g, hg, fun x hx ↦ ?_⟩
    by_cases h : x = p
    · exact h ▸ hgp
    · exact hgs x (Finset.mem_erase.mpr ⟨h, hx⟩)
  rw [not_not] at hgp
  -- every other point contains a homogeneous element outside `p`
  have hx (x : s.erase p) : ∃ e, ∃ h ∈ 𝒜 e, h ∈ x.1.asHomogeneousIdeal ∧
      h ∉ p.asHomogeneousIdeal := by
    have hle : ¬ x.1.asHomogeneousIdeal ≤ p.asHomogeneousIdeal := fun hle ↦
      (Finset.mem_erase.mp x.2).1 (le_antisymm hle (hp.2 (Finset.mem_erase.mp x.2).2 hle))
    obtain ⟨a, hax, hap⟩ := IsConcreteLE.not_le_iff_exists.mp hle
    by_contra! H
    refine hap ?_
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    exact p.1.toIdeal.sum_mem fun i _ ↦
      H i _ (SetLike.coe_mem _) (x.1.asHomogeneousIdeal.2 i hax)
  choose e h hh hhx hhp using hx
  obtain ⟨e₀, he₀, h₀, hh₀, hh₀p⟩ := p.exists_homogeneous_notMem
  set E := e₀ + ∑ x ∈ (s.erase p).attach, e x
  set y := h₀ * ∏ x ∈ (s.erase p).attach, h x
  have hy : y ∈ 𝒜 E := SetLike.mul_mem_graded hh₀ (SetLike.prod_mem_graded _ _ _ (fun x _ ↦ hh x))
  have hyp : y ∉ p.asHomogeneousIdeal := by
    refine p.isPrime.mul_notMem hh₀p ?_
    rw [Ideal.IsPrime.prod_mem_iff (hp := p.isPrime)]
    push Not
    exact fun x _ ↦ hhp x
  have hyx (x : s.erase p) : y ∈ x.1.asHomogeneousIdeal :=
    Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ x))
      (hhx x))
  have hE : 0 < E := lt_of_lt_of_le he₀ (Nat.le_add_right _ _)
  refine ⟨d * E, Nat.mul_pos hd hE, g ^ E + y ^ d, add_mem ?_ ?_, fun x hx ↦ ?_⟩
  · simpa [mul_comm] using SetLike.pow_mem_graded E hg
  · simpa using SetLike.pow_mem_graded d hy
  · by_cases hxp : x = p
    · subst hxp
      intro hmem
      exact hyp (x.isPrime.mem_of_pow_mem d ((Ideal.add_mem_iff_right _
        (Ideal.pow_mem_of_mem _ hgp E hE)).mp hmem))
    · have hxe : x ∈ s.erase p := Finset.mem_erase.mpr ⟨hxp, hx⟩
      intro hmem
      exact hgs x hxe (x.isPrime.mem_of_pow_mem E ((Ideal.add_mem_iff_left _
        (Ideal.pow_mem_of_mem _ (hyx ⟨x, hxe⟩) d hd)).mp hmem))

end ProjectiveSpectrum
