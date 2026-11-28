import Langlands.LinearAlgebra.GMFamilyCentralSubspaceChambers

/-! # Special coarse subspaces and the affine vertex sum -/

noncomputable section

open scoped RealInnerProductSpace
open Classical Module Submodule
open Langlands.LinearAlgebra.AffineVertexWeights Langlands.LinearAlgebra.FiniteHyperplaneSegment

namespace Langlands.GMFamily

/-- A finite family is linearly independent when every linear relation forces a relation among
coefficient vectors that are triangular for a height function. -/
theorem linearIndependent_of_height_triangular {ι J W : Type*} [Fintype ι] [Fintype J]
    [AddCommGroup W] [Module ℝ W] (v : ι → W) (U : ι → J → ℝ) (ht : ι → ℝ)
    (hcomb : ∀ t : ι → ℝ, ∑ c, t c • v c = 0 → ∀ j, ∑ c, t c * U c j = 0)
    (hdiag : ∀ c, ∃ j, U c j ≠ 0 ∧ ∀ c', U c' j ≠ 0 → c' = c ∨ ht c < ht c') :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro t ht0
  by_contra hne
  push Not at hne
  let S := (Finset.univ : Finset ι).filter (fun c => t c ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨c, hc⟩ := hne
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  obtain ⟨c₀, hc₀, hmax⟩ := S.exists_max_image ht hS
  obtain ⟨j, hj, hj'⟩ := hdiag c₀
  have hsum := hcomb t ht0 j
  rw [Finset.sum_eq_single c₀] at hsum
  · exact (Finset.mem_filter.mp hc₀).2 ((mul_eq_zero.mp hsum).resolve_right hj)
  · intro c _ hc
    by_cases htc : t c = 0
    · rw [htc, zero_mul]
    · by_cases hU : U c j = 0
      · rw [hU, mul_zero]
      · rcases hj' c hU with h | h
        · exact (hc h).elim
        · exact ((hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htc⟩)).not_gt h).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {R : Finset E} {a a₁ : Submodule ℝ E} {ξ : E} {P S : Finset E}

/-- Arthur's special subspace condition for `a ⊆ a₁`: positive weights on the roots, and for
every nonzero restriction `β` to `a` the weighted sum of the restrictions to `a₁` of the roots
over `β` lies in `a`. -/
def IsSpecialSubspace (R : Finset E) (a a₁ : Submodule ℝ E) (m : E → ℝ) : Prop :=
  (∀ r ∈ R, 0 < m r) ∧ ∀ β : a, β ≠ 0 →
    (∑ r ∈ R.filter (fun r => restrictedRoot a r = β), m r • a₁.starProjection r) ∈ a

namespace SpecialSlice

private theorem pairing_zero_of_projection_zero {a : Submodule ℝ E} {r p : E}
    (rp : restrictedRoot a r = 0) (hp : p ∈ a) : ⟪r, p⟫ = 0 := by
  rw [← inner_restrictedRoot hp, rp, Submodule.coe_zero, inner_zero_left]

private theorem parabolic_subset_rootSet {a : Submodule ℝ E} {T : Finset E}
    (hT : T ∈ parabolics R a) : T ⊆ R := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1

/-- The restriction of a fine positive root is a natural combination of the fine simple roots. -/
theorem exists_nat_coeffs (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (hP : P ∈ parabolics R a₁)
    {r : E} (hr : r ∈ P) :
    ∃ n : simpleRoots a₁ P → ℕ,
      (restrictedRoot a₁ r : E) = ∑ j, (n j : ℝ) • ((j : a₁) : E) := by
  obtain ⟨n, hn⟩ := (AddSubmonoid.mem_closure_range_iff_of_fintype).mp
    (restrictedRoot_mem_simpleRoot_closure hR ha₁ hP hr)
  exact ⟨n, hn.trans (Finset.sum_congr rfl fun j _ => (Nat.cast_smul_eq_nsmul ℝ _ _).symm)⟩

/-- Chosen natural coefficients of a fine positive root, and `0` outside the chamber. -/
def natCoeff (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (hP : P ∈ parabolics R a₁) (r : E)
    (j : simpleRoots a₁ P) : ℕ :=
  if h : r ∈ P then (exists_nat_coeffs hR ha₁ hP h).choose j else 0

theorem natCoeff_spec (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (hP : P ∈ parabolics R a₁)
    {r : E} (hr : r ∈ P) :
    (restrictedRoot a₁ r : E) = ∑ j, (natCoeff hR ha₁ hP r j : ℝ) • ((j : a₁) : E) := by
  simp only [natCoeff, hr, ↓reduceDIte]
  exact (exists_nat_coeffs hR ha₁ hP hr).choose_spec

/-- The distinct nonzero projected fine simple roots. -/
def sliceValues (R : Finset E) (a a₁ : Submodule ℝ E) (P : Finset E) :
    Finset (noncentral R a) :=
  (Finset.univ.image (sliceNormal R a a₁ (P := P))).erase 0

section Heights

variable {p : E}

theorem inner_simple_nonneg (hpa₁ : p ∈ a₁)
    (hcl : ∀ r ∈ P, 0 ≤ ⟪r, p⟫) (j : simpleRoots a₁ P) : 0 ≤ ⟪((j : a₁) : E), p⟫ := by
  obtain ⟨r, hr, he⟩ := exists_root_of_mem_simpleRoots j
  rw [← he, inner_restrictedRoot hpa₁]
  exact hcl r hr

theorem inner_simple_pos (hP : P ∈ parabolics R a₁) (hle : a ≤ a₁) (hreg : IsRegular R a p)
    (hcl : ∀ r ∈ P, 0 ≤ ⟪r, p⟫) (j : simpleRoots a₁ P)
    (hj : restrictedRoot a ((j : a₁) : E) ≠ 0) : 0 < ⟪((j : a₁) : E), p⟫ := by
  obtain ⟨r, hr, he⟩ := exists_root_of_mem_simpleRoots j
  have hra : restrictedRoot a r ≠ 0 := by rwa [← he, restrictedRoot_nested hle] at hj
  rw [← he, inner_restrictedRoot (hle hreg.1)]
  exact lt_of_le_of_ne (hcl r hr) (hreg.2 r (parabolic_subset_rootSet hP hr) hra).symm

end Heights

/-- The roots whose restriction to `a` is a given vector. -/
def fibre (R : Finset E) (a : Submodule ℝ E) (v : E) : Finset E :=
  R.filter (fun r => (restrictedRoot a r : E) = v)

theorem mem_fibre {v r : E} : r ∈ fibre R a v ↔ r ∈ R ∧ (restrictedRoot a r : E) = v :=
  Finset.mem_filter

theorem coe_restrictedRoot_eq_starProjection (a : Submodule ℝ E) (x : E) :
    (restrictedRoot a x : E) = a.starProjection x := rfl

/-- In a special subspace, a nonzero coarse value is the normalized weighted sum of the fine
restrictions in its fibre, expanded in the fine simple roots. -/
theorem coarse_value_eq_sum (hR : IsRootSet R) (ha₁ : IsLeviSpace R a₁) (hle : a ≤ a₁)
    {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m) (hP : P ∈ parabolics R a₁)
    {β : a} (hβ : β ≠ 0) (hF : ∀ r ∈ fibre R a (β : E), r ∈ P)
    (hne : (fibre R a (β : E)).Nonempty) :
    (β : E) = ∑ j, ((∑ r ∈ fibre R a (β : E), m r)⁻¹ *
      ∑ r ∈ fibre R a (β : E), m r * (natCoeff hR ha₁ hP r j : ℝ)) • ((j : a₁) : E) := by
  set F := fibre R a (β : E) with hFdef
  set N := ∑ r ∈ F, m r with hNdef
  have hN : 0 < N := Finset.sum_pos (fun r hr => hm.1 r (mem_fibre.mp hr).1) hne
  have hfilter : R.filter (fun r => restrictedRoot a r = β) = F := by
    apply Finset.filter_congr
    intro r _
    exact Subtype.ext_iff
  have hX := hm.2 β hβ
  rw [hfilter] at hX
  have hproj : a.starProjection (∑ r ∈ F, m r • a₁.starProjection r) =
      ∑ r ∈ F, m r • a₁.starProjection r :=
    (Submodule.starProjection_eq_self_iff).mpr hX
  have hleft : a.starProjection (∑ r ∈ F, m r • a₁.starProjection r) = N • (β : E) := by
    rw [map_sum, hNdef, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [map_smul, ← coe_restrictedRoot_eq_starProjection a₁ r,
      ← coe_restrictedRoot_eq_starProjection a, restrictedRoot_nested hle, (mem_fibre.mp hr).2]
  have hright : ∑ r ∈ F, m r • a₁.starProjection r =
      ∑ j, (∑ r ∈ F, m r * (natCoeff hR ha₁ hP r j : ℝ)) • ((j : a₁) : E) := by
    calc ∑ r ∈ F, m r • a₁.starProjection r
        = ∑ r ∈ F, m r • ∑ j, (natCoeff hR ha₁ hP r j : ℝ) • ((j : a₁) : E) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← coe_restrictedRoot_eq_starProjection, natCoeff_spec hR ha₁ hP (hF r hr)]
      _ = ∑ j, (∑ r ∈ F, m r * (natCoeff hR ha₁ hP r j : ℝ)) • ((j : a₁) : E) := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          exact Finset.sum_comm
  have hNβ : N • (β : E) = ∑ j, (∑ r ∈ F, m r * (natCoeff hR ha₁ hP r j : ℝ)) • ((j : a₁) : E) :=
    hleft.symm.trans (hproj.trans hright)
  calc (β : E) = N⁻¹ • (N • (β : E)) := by rw [smul_smul, inv_mul_cancel₀ hN.ne', one_smul]
    _ = _ := by
      rw [hNβ, Finset.smul_sum]
      simp_rw [smul_smul]

section Values

variable (D : CentralSubspaceDescent.DescentPosition R a a₁ ξ)
include D

omit D in
theorem mem_sliceValues_iff {P : Finset E} {c : noncentral R a} :
    c ∈ sliceValues R a a₁ P ↔ c ≠ 0 ∧ ∃ j : simpleRoots a₁ P, sliceNormal R a a₁ j = c := by
  simp [sliceValues]

/-- The coarse value of a projected fine simple root is the restriction of that root to `a`. -/
theorem coe_value_eq (hP : P ∈ parabolics R a₁) {j : simpleRoots a₁ P} {c : noncentral R a}
    (hj : sliceNormal R a a₁ j = c) : (c : E) = (restrictedRoot a ((j : a₁) : E) : E) := by
  rw [← hj, CentralSubspaceDescent.coe_sliceNormal_eq_restrictedRoot D hP]

theorem natCoeff_self (hP : P ∈ parabolics R a₁) {j : simpleRoots a₁ P} {r : E} (hr : r ∈ P)
    (he : restrictedRoot a₁ r = (j : a₁)) :
    (natCoeff D.roots D.fine hP r j : ℝ) = 1 := by
  have hli := (simpleRoots_basis D.roots D.fine hP).1
  have h1 := natCoeff_spec D.roots D.fine hP hr
  rw [he] at h1
  have h2 : ((j : a₁) : E) = ∑ i, (if i = j then (1 : ℝ) else 0) • ((i : a₁) : E) := by
    simp
  have := hli.eq_coords_of_eq (h1.symm.trans h2) j
  simpa using this

/-- Distinct nonzero projections of the fine simple roots of a chamber whose closure contains a
coarse chamber are linearly independent in a special subspace. -/
theorem linearIndependent_sliceValues {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P) :
    LinearIndependent ℝ (fun c : sliceValues R a a₁ P => ((c : noncentral R a) : E)) := by
  obtain ⟨p, hp, rfl⟩ := mem_parabolics_iff.mp hS
  have hcl := closure_of_positive_subset D.roots hP hSP
  have hpa₁ : p ∈ a₁ := D.le_fine hp.1
  have hli := (simpleRoots_basis D.roots D.fine hP).1
  -- the height of a fine simple root with nonzero projection is positive
  have hpos (j : simpleRoots a₁ P) (hj : restrictedRoot a ((j : a₁) : E) ≠ 0) :
      0 < ⟪((j : a₁) : E), p⟫ := inner_simple_pos hP D.le_fine hp hcl j hj
  have hnn (j : simpleRoots a₁ P) : 0 ≤ ⟪((j : a₁) : E), p⟫ := inner_simple_nonneg hpa₁ hcl j
  -- data of each value
  have hval (c : sliceValues R a a₁ P) :
      (c : noncentral R a) ≠ 0 ∧ ∃ j : simpleRoots a₁ P, sliceNormal R a a₁ j = c :=
    mem_sliceValues_iff.mp c.prop
  let β (c : sliceValues R a a₁ P) : a := ⟨((c : noncentral R a) : E), (c : noncentral R a).prop.1⟩
  have hβ (c : sliceValues R a a₁ P) : β c ≠ 0 := by
    intro h
    apply (hval c).1
    apply Subtype.ext
    exact congrArg (fun x : a => (x : E)) h
  have hβE (c : sliceValues R a a₁ P) : ((β c : a) : E) = ((c : noncentral R a) : E) := rfl
  have hfib (c : sliceValues R a a₁ P) : ∀ r ∈ fibre R a ((β c : a) : E), r ∈ P := by
    intro r hr
    obtain ⟨hrR, hre⟩ := mem_fibre.mp hr
    obtain ⟨j, hj⟩ := (hval c).2
    have hc := coe_value_eq D hP hj
    have hjz : restrictedRoot a ((j : a₁) : E) ≠ 0 := by
      intro h0
      apply (hval c).1
      apply Subtype.ext
      rw [hc, h0]
      rfl
    apply hSP
    refine mem_posSet_iff.mpr ⟨hrR, ?_⟩
    rw [← inner_restrictedRoot hp.1, hre, hβE, hc, inner_restrictedRoot hp.1]
    exact hpos j hjz
  have hrep (c : sliceValues R a a₁ P) :
      ∃ j : simpleRoots a₁ P, sliceNormal R a a₁ j = c ∧ ∃ r ∈ P,
        restrictedRoot a₁ r = (j : a₁) ∧ r ∈ fibre R a ((β c : a) : E) := by
    obtain ⟨j, hj⟩ := (hval c).2
    obtain ⟨r, hr, he⟩ := exists_root_of_mem_simpleRoots j
    refine ⟨j, hj, r, hr, he, mem_fibre.mpr ⟨parabolic_subset_rootSet hP hr, ?_⟩⟩
    rw [hβE, coe_value_eq D hP hj, ← he, restrictedRoot_nested D.le_fine]
  let F (c : sliceValues R a a₁ P) := fibre R a ((β c : a) : E)
  let N (c : sliceValues R a a₁ P) := ∑ r ∈ F c, m r
  let U (c : sliceValues R a a₁ P) (j : simpleRoots a₁ P) : ℝ :=
    (N c)⁻¹ * ∑ r ∈ F c, m r * (natCoeff D.roots D.fine hP r j : ℝ)
  have hU (c : sliceValues R a a₁ P) :
      ((c : noncentral R a) : E) = ∑ j, U c j • ((j : a₁) : E) := by
    obtain ⟨_, _, r, _, _, hrF⟩ := hrep c
    exact coarse_value_eq_sum D.roots D.fine D.le_fine hm hP (hβ c) (hfib c) ⟨r, hrF⟩
  apply linearIndependent_of_height_triangular _ U (fun c => ⟪((c : noncentral R a) : E), p⟫)
  · intro t ht j
    have hsum : ∑ i, (∑ c, t c * U c i) • ((i : a₁) : E) = 0 := by
      rw [← ht]
      simp_rw [hU, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (Fintype.linearIndependent_iff.mp hli) _ hsum j
  · intro c
    obtain ⟨j, hj, rj, hrj, hej, hrjF⟩ := hrep c
    have hc := coe_value_eq D hP hj
    have hjz : restrictedRoot a ((j : a₁) : E) ≠ 0 := by
      intro h0
      apply (hval c).1
      apply Subtype.ext
      rw [hc, h0]
      rfl
    have hN : 0 < N c := Finset.sum_pos (fun r hr => hm.1 r (mem_fibre.mp hr).1) ⟨rj, hrjF⟩
    have hterm_nn (c' : sliceValues R a a₁ P) (r : E) (hr : r ∈ F c') :
        0 ≤ m r * (natCoeff D.roots D.fine hP r j : ℝ) :=
      mul_nonneg (hm.1 r (mem_fibre.mp hr).1).le (Nat.cast_nonneg _)
    refine ⟨j, ?_, ?_⟩
    · apply mul_ne_zero (inv_ne_zero hN.ne')
      apply ne_of_gt
      apply Finset.sum_pos' (hterm_nn c)
      refine ⟨rj, hrjF, ?_⟩
      rw [natCoeff_self D hP hrj hej, mul_one]
      exact hm.1 rj (mem_fibre.mp hrjF).1
    · intro c' hc'
      have hsum : ∑ r ∈ F c', m r * (natCoeff D.roots D.fine hP r j : ℝ) ≠ 0 :=
        fun h0 => hc' (by simp only [U, h0, mul_zero])
      obtain ⟨r, hrF, hrne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      have hrP := hfib c' r hrF
      have hnj : (natCoeff D.roots D.fine hP r j : ℝ) ≠ 0 := fun h0 => hrne (by rw [h0, mul_zero])
      have hnj1 : (1 : ℝ) ≤ natCoeff D.roots D.fine hP r j := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hnj (by simp [h]))
      -- the height of `c'`
      have hc'r : ((c' : noncentral R a) : E) = (restrictedRoot a r : E) :=
        ((mem_fibre.mp hrF).2).symm
      have hht' : ⟪((c' : noncentral R a) : E), p⟫ =
          ∑ i, (natCoeff D.roots D.fine hP r i : ℝ) * ⟪((i : a₁) : E), p⟫ := by
        rw [hc'r, inner_restrictedRoot hp.1, ← inner_restrictedRoot hpa₁,
          natCoeff_spec D.roots D.fine hP hrP, sum_inner]
        simp_rw [real_inner_smul_left]
      have hht : ⟪((c : noncentral R a) : E), p⟫ = ⟪((j : a₁) : E), p⟫ := by
        rw [hc, inner_restrictedRoot hp.1]
      have hterms (i : simpleRoots a₁ P) :
          0 ≤ (natCoeff D.roots D.fine hP r i : ℝ) * ⟪((i : a₁) : E), p⟫ :=
        mul_nonneg (Nat.cast_nonneg _) (hnn i)
      by_contra hcon
      push Not at hcon
      obtain ⟨hne', hle'⟩ := hcon
      rw [hht, hht'] at hle'
      -- every other simple root in the expansion projects to zero, and `j` occurs once
      have hpair (i : simpleRoots a₁ P) (hij : i ≠ j) :
          (natCoeff D.roots D.fine hP r i : ℝ) * ⟪((i : a₁) : E), p⟫ = 0 := by
        by_contra hi
        have hsub : ({i, j} : Finset (simpleRoots a₁ P)) ⊆ Finset.univ := Finset.subset_univ _
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hterms x)
        rw [Finset.sum_pair hij] at h2
        have hjj : ⟪((j : a₁) : E), p⟫ ≤
            (natCoeff D.roots D.fine hP r j : ℝ) * ⟪((j : a₁) : E), p⟫ := by
          nlinarith [hnn j]
        have hipos := lt_of_le_of_ne (hterms i) (Ne.symm hi)
        linarith
      have hj1 : (natCoeff D.roots D.fine hP r j : ℝ) = 1 := by
        have hsub : ({j} : Finset (simpleRoots a₁ P)) ⊆ Finset.univ := Finset.subset_univ _
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hterms x)
        rw [Finset.sum_singleton] at h2
        have hjp := hpos j hjz
        by_contra hj1
        have hgt : (1 : ℝ) < natCoeff D.roots D.fine hP r j := lt_of_le_of_ne hnj1 (Ne.symm hj1)
        nlinarith
      apply hne'
      apply Subtype.ext
      apply Subtype.ext
      rw [hc'r, hc, ← restrictedRoot_nested D.le_fine r, natCoeff_spec D.roots D.fine hP hrP]
      rw [coe_restrictedRoot_eq_starProjection, coe_restrictedRoot_eq_starProjection, map_sum]
      rw [Finset.sum_eq_single j]
      · rw [map_smul, hj1, one_smul]
      · intro i _ hij
        have hz := hpair i hij
        rcases mul_eq_zero.mp hz with h | h
        · rw [h, zero_smul, map_zero]
        · have hproj : restrictedRoot a ((i : a₁) : E) = 0 := by
            by_contra hne
            exact (hpos i hne).ne' h
          rw [map_smul, ← coe_restrictedRoot_eq_starProjection, hproj, Submodule.coe_zero, smul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim

omit D in
/-- Grouping a combination of the projected fine simple roots by their values. -/
theorem sum_sliceNormal_eq_sum_values (n : simpleRoots a₁ P → ℝ) :
    ∑ i, n i • ((sliceNormal R a a₁ i : noncentral R a) : E) =
      ∑ c ∈ sliceValues R a a₁ P,
        (∑ i ∈ Finset.univ.filter (fun i => sliceNormal R a a₁ i = c), n i) •
          ((c : noncentral R a) : E) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image (sliceNormal R a a₁ (P := P))) (g := sliceNormal R a a₁)
    (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  have hG (c : noncentral R a) :
      ∑ i ∈ Finset.univ.filter (fun i => sliceNormal R a a₁ i = c),
          n i • ((sliceNormal R a a₁ i : noncentral R a) : E) =
        (∑ i ∈ Finset.univ.filter (fun i => sliceNormal R a a₁ i = c), n i) •
          ((c : noncentral R a) : E) := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  simp_rw [hG]
  rw [sliceValues, Finset.sum_erase]
  simp

/-- The restriction to `a` of a fine positive root, written through the projected simple roots. -/
theorem restrictedRoot_eq_sum_sliceNormal (hP : P ∈ parabolics R a₁) {r : E} (hr : r ∈ P) :
    (restrictedRoot a r : E) =
      ∑ i, (natCoeff D.roots D.fine hP r i : ℝ) • ((sliceNormal R a a₁ i : noncentral R a) : E) := by
  rw [← restrictedRoot_nested D.le_fine r, coe_restrictedRoot_eq_starProjection,
    natCoeff_spec D.roots D.fine hP hr, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, ← coe_restrictedRoot_eq_starProjection, CentralSubspaceDescent.coe_sliceNormal_eq_restrictedRoot D hP]

/-- Natural coefficients of a fine positive root, grouped by the projected values. -/
def valueCoeff (hP : P ∈ parabolics R a₁) (r : E) (c : noncentral R a) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => sliceNormal R a a₁ i = c), natCoeff D.roots D.fine hP r i

theorem restrictedRoot_eq_sum_values (hP : P ∈ parabolics R a₁) {r : E} (hr : r ∈ P) :
    (restrictedRoot a r : E) =
      ∑ c ∈ sliceValues R a a₁ P, (valueCoeff D hP r c : ℝ) • ((c : noncentral R a) : E) := by
  rw [restrictedRoot_eq_sum_sliceNormal D hP hr, sum_sliceNormal_eq_sum_values]
  simp [valueCoeff]

/-- Coefficients in the independent family of values are determined. -/
theorem coeffs_eq_of_sum_eq {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P)
    {f g : noncentral R a → ℝ}
    (he : ∑ c ∈ sliceValues R a a₁ P, f c • ((c : noncentral R a) : E) =
      ∑ c ∈ sliceValues R a a₁ P, g c • ((c : noncentral R a) : E))
    {c : noncentral R a} (hc : c ∈ sliceValues R a a₁ P) : f c = g c := by
  have hli := linearIndependent_sliceValues D hm hS hP hSP
  rw [← Finset.sum_coe_sort (sliceValues R a a₁ P) (fun c => f c • ((c : noncentral R a) : E)),
    ← Finset.sum_coe_sort (sliceValues R a a₁ P) (fun c => g c • ((c : noncentral R a) : E))]
    at he
  exact hli.eq_coords_of_eq (f := fun c => f c) (g := fun c => g c) he ⟨c, hc⟩

/-- Each projected value is a coarse simple root. -/
theorem value_mem_simpleRoots {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P)
    {c : noncentral R a} (hc : c ∈ sliceValues R a a₁ P) :
    (⟨(c : E), c.prop.1⟩ : a) ∈ simpleRoots a S := by
  obtain ⟨p, hp, hSp⟩ := mem_parabolics_iff.mp hS
  have hcl := closure_of_positive_subset D.roots hP (hSp ▸ hSP)
  obtain ⟨hc0, j, hj⟩ := mem_sliceValues_iff.mp hc
  obtain ⟨rj, hrj, hej⟩ := exists_root_of_mem_simpleRoots j
  have hcE : (c : E) = (restrictedRoot a rj : E) := by
    rw [coe_value_eq D hP hj, ← hej, restrictedRoot_nested D.le_fine]
  have hjz : restrictedRoot a rj ≠ 0 := by
    intro h0
    apply hc0
    apply Subtype.ext
    rw [hcE, h0]
    rfl
  have hpos_of (r : E) (hrR : r ∈ R) (hr0 : restrictedRoot a r ≠ 0) (hrP : r ∈ P) :
      r ∈ S := by
    rw [hSp]
    exact mem_posSet_iff.mpr ⟨hrR, lt_of_le_of_ne (hcl r hrP) (hp.2 r hrR hr0).symm⟩
  have hrjS : rj ∈ S := hpos_of rj (parabolic_subset_rootSet hP hrj) hjz hrj
  have hval : restrictedRoot a rj = (⟨(c : E), c.prop.1⟩ : a) := Subtype.ext hcE.symm
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨rj, hrjS, hval⟩, ?_⟩
  rintro ⟨u, hu, w, hw, he⟩
  obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨r'', hr'', rfl⟩ := Finset.mem_image.mp hw
  have hE : (c : E) = (restrictedRoot a r' : E) + (restrictedRoot a r'' : E) := by
    have := congrArg (fun x : a => (x : E)) he
    simpa using this
  rw [restrictedRoot_eq_sum_values D hP (hSP hr'), restrictedRoot_eq_sum_values D hP (hSP hr''),
    ← Finset.sum_add_distrib] at hE
  simp_rw [← add_smul] at hE
  have hind : (c : E) = ∑ c' ∈ sliceValues R a a₁ P,
      (if c' = c then (1 : ℝ) else 0) • ((c' : noncentral R a) : E) := by
    simp_rw [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' (sliceValues R a a₁ P) c]
    simp [hc]
  have hcoef (c' : noncentral R a) (hc' : c' ∈ sliceValues R a a₁ P) :
      ((valueCoeff D hP r' c' : ℝ) + valueCoeff D hP r'' c') = if c' = c then 1 else 0 :=
    coeffs_eq_of_sum_eq D hm hS hP hSP (hE.symm.trans hind) hc'
  -- one of the two roots has no coefficient left, so its restriction vanishes
  have hzero_of (r : E) (hr : r ∈ S) (hK : ∀ c' ∈ sliceValues R a a₁ P, valueCoeff D hP r c' = 0) :
      False := by
    have h0 := restrictedRoot_eq_sum_values D hP (hSP hr)
    rw [Finset.sum_eq_zero (fun c' hc' => by rw [hK c' hc', Nat.cast_zero, zero_smul])] at h0
    have hrp := (mem_posSet_iff.mp (hSp ▸ hr)).2
    rw [← inner_restrictedRoot hp.1, h0, inner_zero_left] at hrp
    exact lt_irrefl _ hrp
  have hc1 := hcoef c hc
  simp only [↓reduceIte] at hc1
  have hc1' : valueCoeff D hP r' c + valueCoeff D hP r'' c = 1 := by exact_mod_cast hc1
  have hoff (c' : noncentral R a) (hc' : c' ∈ sliceValues R a a₁ P) (hne : c' ≠ c) :
      valueCoeff D hP r' c' = 0 ∧ valueCoeff D hP r'' c' = 0 := by
    have h := hcoef c' hc'
    simp only [hne, ↓reduceIte] at h
    have h' : valueCoeff D hP r' c' + valueCoeff D hP r'' c' = 0 := by exact_mod_cast h
    omega
  rcases Nat.eq_zero_or_pos (valueCoeff D hP r' c) with h0 | h0
  · exact hzero_of r' hr' fun c' hc' => by
      by_cases hne : c' = c
      · rw [hne, h0]
      · exact (hoff c' hc' hne).1
  · have h0' : valueCoeff D hP r'' c = 0 := by omega
    exact hzero_of r'' hr'' fun c' hc' => by
      by_cases hne : c' = c
      · rw [hne, h0']
      · exact (hoff c' hc' hne).2

omit D in
theorem restrictedRoot_add (a : Submodule ℝ E) (u w : E) :
    restrictedRoot a (u + w) = restrictedRoot a u + restrictedRoot a w := by
  simp [restrictedRoot, map_add]

/-- Each coarse simple root is the projection of a fine simple root of a chamber containing the
coarse chamber. -/
theorem exists_value_of_mem_simpleRoots (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁)
    (hSP : S ⊆ P) {b : a} (hb : b ∈ simpleRoots a S) :
    ∃ c ∈ sliceValues R a a₁ P, ((c : noncentral R a) : E) = (b : E) := by
  obtain ⟨p, hp, hSp⟩ := mem_parabolics_iff.mp hS
  have hcl := closure_of_positive_subset D.roots hP (hSp ▸ hSP)
  have hpa₁ : p ∈ a₁ := D.le_fine hp.1
  obtain ⟨q, hq, hPq⟩ := mem_parabolics_iff.mp hP
  obtain ⟨h, hh, hqh⟩ := exists_regular_ambient_chamber D.roots q
  have ha₁q : a₁ = leviSpaceOf R q := (leviSpaceOf_eq_of_isRegular D.fine hq).symm
  have hfine := simpleRoots_posSet_eq_image D.roots hh hqh ha₁q
  obtain ⟨hbR, hbind⟩ := Finset.mem_filter.mp hb
  obtain ⟨r, hrS, hrb⟩ := Finset.mem_image.mp hbR
  -- ambient positive roots are nonnegative at the coarse point
  have hamb (x : E) (hx : x ∈ R) (hxh : 0 < ⟪x, h⟫) : 0 ≤ ⟪x, p⟫ := by
    by_cases hx1 : restrictedRoot a₁ x = 0
    · rw [pairing_zero_of_projection_zero hx1 hpa₁]
    · have hxq : 0 ≤ ⟪x, q⟫ := hqh x (mem_posSet_iff.mpr ⟨hx, hxh⟩)
      have hxq' : 0 < ⟪x, q⟫ := lt_of_le_of_ne hxq (hq.2 x hx hx1).symm
      exact hcl x (hPq ▸ mem_posSet_iff.mpr ⟨hx, hxq'⟩)
  have hSR : S ⊆ R := parabolic_subset_rootSet hS
  have hpos_S (x : E) (hx : x ∈ S) : 0 < ⟪x, p⟫ := (mem_posSet_iff.mp (hSp ▸ hx)).2
  have hmemS (x : E) (hx : x ∈ R) (hxh : 0 < ⟪x, h⟫) (hx0 : restrictedRoot a x ≠ 0) : x ∈ S :=
    hSp ▸ mem_posSet_iff.mpr ⟨hx, lt_of_le_of_ne (hamb x hx hxh) (hp.2 x hx hx0).symm⟩
  let Fb := S.filter (fun x => restrictedRoot a x = b)
  have hFb : Fb.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨hrS, hrb⟩⟩
  obtain ⟨r₀, hr₀, hmin⟩ := Fb.exists_min_image (fun x => ⟪x, h⟫) hFb
  obtain ⟨hr₀S, hr₀b⟩ := Finset.mem_filter.mp hr₀
  have hr₀R := hSR hr₀S
  have hr₀P : r₀ ∈ P := hSP hr₀S
  have hr₀q : 0 < ⟪r₀, q⟫ := (mem_posSet_iff.mp (hPq ▸ hr₀P)).2
  have hr₀h : 0 < ⟪r₀, h⟫ := by
    rcases lt_or_gt_of_ne (hh r₀ hr₀R) with hn | hpos
    · have hneg : -r₀ ∈ posSet R h := mem_posSet_iff.mpr ⟨neg_mem_rootSet D.roots hr₀R,
        by rw [inner_neg_left]; linarith⟩
      have := hqh (-r₀) hneg
      rw [inner_neg_left] at this
      linarith
    · exact hpos
  have hb0 : b ≠ 0 := by
    intro h0
    have := hpos_S r₀ hr₀S
    rw [← inner_restrictedRoot hp.1, hr₀b, h0, Submodule.coe_zero, inner_zero_left] at this
    exact lt_irrefl _ this
  have hsimple : r₀ ∈ positiveSimpleRoots R h := by
    refine Finset.mem_filter.mpr ⟨mem_posSet_iff.mpr ⟨hr₀R, hr₀h⟩, ?_⟩
    rintro ⟨u, hu, w, hw, he⟩
    obtain ⟨huR, huh⟩ := mem_posSet_iff.mp hu
    obtain ⟨hwR, hwh⟩ := mem_posSet_iff.mp hw
    have hsum : restrictedRoot a u + restrictedRoot a w = b := by
      rw [← restrictedRoot_add, ← he, hr₀b]
    have hlt_u : ⟪w, h⟫ < ⟪r₀, h⟫ := by rw [he, inner_add_left]; linarith
    have hlt_w : ⟪u, h⟫ < ⟪r₀, h⟫ := by rw [he, inner_add_left]; linarith
    by_cases hu0 : restrictedRoot a u = 0
    · rw [hu0, zero_add] at hsum
      have hwS : w ∈ S := hmemS w hwR hwh (by rw [hsum]; exact hb0)
      have := hmin w (Finset.mem_filter.mpr ⟨hwS, hsum⟩)
      linarith
    · by_cases hw0 : restrictedRoot a w = 0
      · rw [hw0, add_zero] at hsum
        have huS : u ∈ S := hmemS u huR huh hu0
        have := hmin u (Finset.mem_filter.mpr ⟨huS, hsum⟩)
        linarith
      · exact hbind ⟨restrictedRoot a u, Finset.mem_image.mpr ⟨u, hmemS u huR huh hu0, rfl⟩,
          restrictedRoot a w, Finset.mem_image.mpr ⟨w, hmemS w hwR hwh hw0, rfl⟩, hsum.symm⟩
  have hj : restrictedRoot a₁ r₀ ∈ simpleRoots a₁ P := by
    rw [hPq, hfine]
    exact Finset.mem_image.mpr ⟨r₀, Finset.mem_filter.mpr ⟨hsimple, hr₀q.ne'⟩, rfl⟩
  let j : simpleRoots a₁ P := ⟨restrictedRoot a₁ r₀, hj⟩
  have hcE : ((sliceNormal R a a₁ j : noncentral R a) : E) = (b : E) := by
    rw [CentralSubspaceDescent.coe_sliceNormal_eq_restrictedRoot D hP]
    change (restrictedRoot a (restrictedRoot a₁ r₀ : E) : E) = (b : E)
    rw [restrictedRoot_nested D.le_fine, hr₀b]
  refine ⟨sliceNormal R a a₁ j, mem_sliceValues_iff.mpr ⟨?_, j, rfl⟩, hcE⟩
  intro h0
  apply hb0
  apply Subtype.ext
  rw [← hcE, h0]
  rfl

theorem span_sliceValues_eq_top (hP : P ∈ parabolics R a₁) :
    span ℝ (Set.range fun c : sliceValues R a a₁ P => (c : noncentral R a)) = ⊤ := by
  rw [eq_top_iff, ← CentralSubspaceDescent.span_sliceNormal_eq_top D hP, span_le]
  rintro _ ⟨i, rfl⟩
  by_cases h : sliceNormal R a a₁ i = 0
  · rw [h]
    exact Submodule.zero_mem _
  · exact subset_span ⟨⟨sliceNormal R a a₁ i, mem_sliceValues_iff.mpr ⟨h, i, rfl⟩⟩, rfl⟩

/-- The distinct nonzero projections form a basis of the noncentral coarse space. -/
def sliceValuesBasis {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P) :
    Basis (sliceValues R a a₁ P) ℝ (noncentral R a) :=
  Basis.mk (LinearIndependent.of_comp (noncentral R a).subtype
      (linearIndependent_sliceValues D hm hS hP hSP))
    (span_sliceValues_eq_top D hP).ge

theorem card_sliceValues {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P) :
    (sliceValues R a a₁ P).card = finrank ℝ (noncentral R a) := by
  rw [finrank_eq_card_basis (sliceValuesBasis D hm hS hP hSP), Fintype.card_coe]

/-- A basis of projected normals contains exactly one index over each projected value. -/
theorem basisIndex_exists_mem {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P)
    (J : BasisIndex (sliceNormal R a a₁ (P := P))) {k : simpleRoots a₁ P}
    (hk : sliceNormal R a a₁ k ≠ 0) : ∃ i ∈ J.val, sliceNormal R a a₁ i = sliceNormal R a a₁ k := by
  have hsub : J.val.image (sliceNormal R a a₁ (P := P)) ⊆ sliceValues R a a₁ P := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact mem_sliceValues_iff.mpr ⟨J.prop.1.ne_zero ⟨i, hi⟩, i, rfl⟩
  have hinj : Set.InjOn (sliceNormal R a a₁ (P := P)) J.val := by
    intro i hi i' hi' he
    have := J.prop.1.injective (a₁ := ⟨i, hi⟩) (a₂ := ⟨i', hi'⟩) he
    exact congrArg Subtype.val this
  have hcard : (sliceValues R a a₁ P).card ≤ (J.val.image (sliceNormal R a a₁ (P := P))).card := by
    rw [Finset.card_image_of_injOn hinj, J.prop.2, card_sliceValues D hm hS hP hSP]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hkv : sliceNormal R a a₁ k ∈ sliceValues R a a₁ P := mem_sliceValues_iff.mpr ⟨hk, k, rfl⟩
  rw [← heq] at hkv
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hkv
  exact ⟨i, hi, he⟩

omit D in
theorem basisIndex_injOn (J : BasisIndex (sliceNormal R a a₁ (P := P))) {i i' : simpleRoots a₁ P}
    (hi : i ∈ J.val) (hi' : i' ∈ J.val)
    (he : sliceNormal R a a₁ i = sliceNormal R a a₁ i') : i = i' :=
  congrArg Subtype.val (J.prop.1.injective (a₁ := ⟨i, hi⟩) (a₂ := ⟨i', hi'⟩) he)

omit D in
/-- The slack of a nonzero normal outside a basis, through the index of the basis over the same
value. -/
theorem slack_eq_of_same_value (J : BasisIndex (sliceNormal R a a₁ (P := P)))
    {i k : simpleRoots a₁ P} (hi : i ∈ J.val)
    (he : sliceNormal R a a₁ i = sliceNormal R a a₁ k) (h : simpleRoots a₁ P → ℝ) :
    J.slack k h = h k - h i := by
  rw [J.slack_apply, ← he, J.interpolate_apply_of_mem h hi]

end Values

section Offsets

variable (R a a₁)

/-- A fixed enumeration of the fine simple roots. -/
def simpleIndex (P : Finset E) : simpleRoots a₁ P ≃ Fin (Fintype.card (simpleRoots a₁ P)) :=
  Fintype.equivFin _

/-- The index of least enumeration among those with the same projected value. -/
def IsClassRep {P : Finset E} (i : simpleRoots a₁ P) : Prop :=
  ∀ j, sliceNormal R a a₁ j = sliceNormal R a a₁ i → simpleIndex a₁ P i ≤ simpleIndex a₁ P j

/-- Offsets keeping the constant inequalities, vanishing on one index over each value, and
distinct positive elsewhere. -/
def repOffset (ξ : E) {P : Finset E} (i : simpleRoots a₁ P) : ℝ :=
  if sliceNormal R a a₁ i = 0 then sliceOffset ξ i
  else if IsClassRep R a a₁ i then 0 else (simpleIndex a₁ P i : ℝ) + 1

variable {R a a₁}

theorem isClassRep_unique {i j : simpleRoots a₁ P} (hi : IsClassRep R a a₁ i)
    (hj : IsClassRep R a a₁ j) (he : sliceNormal R a a₁ i = sliceNormal R a a₁ j) : i = j := by
  have h1 := hi j he.symm
  have h2 := hj i he
  exact (simpleIndex a₁ P).injective (le_antisymm h1 h2)

theorem exists_isClassRep (k : simpleRoots a₁ P) :
    ∃ i : simpleRoots a₁ P, IsClassRep R a a₁ i ∧ sliceNormal R a a₁ i = sliceNormal R a a₁ k := by
  let T := Finset.univ.filter (fun j : simpleRoots a₁ P => sliceNormal R a a₁ j = sliceNormal R a a₁ k)
  have hT : T.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  obtain ⟨i, hi, hmin⟩ := T.exists_min_image (fun j => simpleIndex a₁ P j) hT
  have hik := (Finset.mem_filter.mp hi).2
  refine ⟨i, fun j hj => hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.trans hik⟩), hik⟩

theorem repOffset_of_zero {i : simpleRoots a₁ P} (h : sliceNormal R a a₁ i = 0) :
    repOffset R a a₁ ξ i = sliceOffset ξ i := by
  simp [repOffset, h]

theorem repOffset_of_rep {i : simpleRoots a₁ P} (h : sliceNormal R a a₁ i ≠ 0)
    (hr : IsClassRep R a a₁ i) : repOffset R a a₁ ξ i = 0 := by
  simp [repOffset, h, hr]

theorem repOffset_of_not_rep {i : simpleRoots a₁ P} (h : sliceNormal R a a₁ i ≠ 0)
    (hr : ¬ IsClassRep R a a₁ i) : repOffset R a a₁ ξ i = (simpleIndex a₁ P i : ℝ) + 1 := by
  simp [repOffset, h, hr]

end Offsets

section VertexSum

variable (D : CentralSubspaceDescent.DescentPosition R a a₁ ξ)
include D

variable {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
  (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P)
include hm hS hP hSP

theorem repOffset_regular :
    Regular (wallForm (sliceNormal R a a₁ (P := P))) (repOffset R a a₁ ξ (P := P)) := by
  rintro ⟨J, k, hk⟩
  change J.slack k (repOffset R a a₁ ξ) ≠ 0
  by_cases h0 : sliceNormal R a a₁ k = 0
  · rw [slack_of_normal_eq_zero J h0, repOffset_of_zero h0]
    have := CentralSubspaceDescent.sliceOffset_regular D hP ⟨J, k, hk⟩
    change J.slack k (sliceOffset ξ) ≠ 0 at this
    rwa [slack_of_normal_eq_zero J h0] at this
  · obtain ⟨i, hi, he⟩ := basisIndex_exists_mem D hm hS hP hSP J h0
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    have hi0 : sliceNormal R a a₁ i ≠ 0 := he ▸ h0
    rw [slack_eq_of_same_value J hi he]
    have hnn (x : simpleRoots a₁ P) : (0 : ℝ) ≤ (simpleIndex a₁ P x : ℝ) := by positivity
    by_cases hkr : IsClassRep R a a₁ k
    · have hir : ¬ IsClassRep R a a₁ i := fun hir => hik (isClassRep_unique hir hkr he)
      rw [repOffset_of_rep h0 hkr, repOffset_of_not_rep hi0 hir]
      have := hnn i
      intro h
      linarith
    · rw [repOffset_of_not_rep h0 hkr]
      by_cases hir : IsClassRep R a a₁ i
      · rw [repOffset_of_rep hi0 hir]
        have := hnn k
        intro h
        linarith
      · rw [repOffset_of_not_rep hi0 hir]
        intro h
        apply hik
        apply (simpleIndex a₁ P).injective
        apply Fin.ext
        have h' : ((simpleIndex a₁ P k : ℕ) : ℝ) = ((simpleIndex a₁ P i : ℕ) : ℝ) := by
          linarith
        exact_mod_cast h'.symm

omit hm hS hP hSP D in
variable (R a a₁) in
/-- The representative indices with nonzero projection. -/
def repSet (P : Finset E) : Finset (simpleRoots a₁ P) :=
  Finset.univ.filter (fun i => sliceNormal R a a₁ i ≠ 0 ∧ IsClassRep R a a₁ i)

omit hm hS hP hSP D in
theorem mem_repSet {i : simpleRoots a₁ P} :
    i ∈ repSet R a a₁ P ↔ sliceNormal R a a₁ i ≠ 0 ∧ IsClassRep R a a₁ i := by
  simp [repSet]

omit hm hS hP hSP D in
/-- The representatives correspond to the projected values. -/
def repValueEquiv (R : Finset E) (a a₁ : Submodule ℝ E) (P : Finset E) :
    repSet R a a₁ P ≃ sliceValues R a a₁ P :=
  Equiv.ofBijective
    (fun i => ⟨sliceNormal R a a₁ (i : simpleRoots a₁ P),
      mem_sliceValues_iff.mpr ⟨(mem_repSet.mp i.prop).1, (i : simpleRoots a₁ P), rfl⟩⟩)
    ⟨fun i j h => by
        have h' : sliceNormal R a a₁ (i : simpleRoots a₁ P) =
            sliceNormal R a a₁ (j : simpleRoots a₁ P) := congrArg Subtype.val h
        exact Subtype.ext (isClassRep_unique (mem_repSet.mp i.prop).2
          (mem_repSet.mp j.prop).2 h'),
      fun c => by
        have hc := mem_sliceValues_iff.mp c.prop
        obtain ⟨k, hk⟩ := hc.2
        obtain ⟨i, hi, he⟩ := exists_isClassRep (R := R) (a := a) k
        refine ⟨⟨i, mem_repSet.mpr ⟨?_, hi⟩⟩, Subtype.ext (he.trans hk)⟩
        rw [he, hk]
        exact hc.1⟩

omit hm hS hP hSP D in
theorem repValueEquiv_apply (i : repSet R a a₁ P) :
    ((repValueEquiv R a a₁ P i : sliceValues R a a₁ P) : noncentral R a) =
      sliceNormal R a a₁ (i : simpleRoots a₁ P) := rfl

omit hm hS hP hSP D in
/-- The representatives form a basis of projected normals. -/
def repBasis (D : CentralSubspaceDescent.DescentPosition R a a₁ ξ) {m : E → ℝ} (hm : IsSpecialSubspace R a a₁ m)
    (hS : S ∈ parabolics R a) (hP : P ∈ parabolics R a₁) (hSP : S ⊆ P) :
    BasisIndex (sliceNormal R a a₁ (P := P)) :=
  ⟨repSet R a a₁ P, by
    have hli := (sliceValuesBasis D hm hS hP hSP).linearIndependent
    have h := hli.comp (repValueEquiv R a a₁ P) (repValueEquiv R a a₁ P).injective
    convert h using 1
    funext i
    simp [sliceValuesBasis, repValueEquiv_apply], by
    rw [← card_sliceValues D hm hS hP hSP, ← Fintype.card_coe (repSet R a a₁ P),
      ← Fintype.card_coe (sliceValues R a a₁ P)]
    exact Fintype.card_congr (repValueEquiv R a a₁ P)⟩

/-- At the representative offsets, a feasible basis is the representative basis. -/
theorem eq_repBasis_of_feasible (J : BasisIndex (sliceNormal R a a₁ (P := P)))
    (hJ : ∀ k ∉ J.val, 0 < J.slack k (repOffset R a a₁ ξ)) : J = repBasis D hm hS hP hSP := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    have hi0 : sliceNormal R a a₁ i ≠ 0 := J.prop.1.ne_zero ⟨i, hi⟩
    refine mem_repSet.mpr ⟨hi0, ?_⟩
    by_contra hir
    obtain ⟨k, hk, he⟩ := exists_isClassRep (R := R) (a := a) i
    have hki : k ≠ i := fun h => hir (h ▸ hk)
    have hkJ : k ∉ J.val := fun hkJ => hki (basisIndex_injOn J hkJ hi he)
    have hs := hJ k hkJ
    rw [slack_eq_of_same_value J hi he.symm, repOffset_of_rep (he ▸ hi0) hk,
      repOffset_of_not_rep hi0 hir] at hs
    have : (0 : ℝ) ≤ (simpleIndex a₁ P i : ℝ) := by positivity
    linarith
  · rw [J.prop.2, (repBasis D hm hS hP hSP).prop.2]

theorem repBasis_feasible_iff :
    (∀ k ∉ (repBasis D hm hS hP hSP).val, 0 < (repBasis D hm hS hP hSP).slack k (repOffset R a a₁ ξ)) ↔
      ∀ k : simpleRoots a₁ P, sliceNormal R a a₁ k = 0 → 0 < sliceOffset ξ k := by
  constructor
  · intro h k hk
    have hkJ : k ∉ (repBasis D hm hS hP hSP).val := fun hm' => (mem_repSet.mp hm').1 hk
    have := h k hkJ
    rwa [slack_of_normal_eq_zero _ hk, repOffset_of_zero hk] at this
  · intro h k hkJ
    by_cases hk : sliceNormal R a a₁ k = 0
    · rw [slack_of_normal_eq_zero _ hk, repOffset_of_zero hk]
      exact h k hk
    · have hkr : ¬ IsClassRep R a a₁ k := fun hkr => hkJ (mem_repSet.mpr ⟨hk, hkr⟩)
      obtain ⟨i, hi, he⟩ := exists_isClassRep (R := R) (a := a) k
      have hiJ : i ∈ (repBasis D hm hS hP hSP).val := mem_repSet.mpr ⟨he ▸ hk, hi⟩
      rw [slack_eq_of_same_value _ hiJ he, repOffset_of_not_rep hk hkr,
        repOffset_of_rep (he ▸ hk) hi]
      have : (0 : ℝ) ≤ (simpleIndex a₁ P k : ℝ) := by positivity
      linarith

theorem vertexSum_repOffset (param : noncentral R a →ₗ[ℝ] ℂ) :
    vertexSum (sliceNormal R a a₁ (P := P)) param (repOffset R a a₁ ξ) =
      if ∀ k : simpleRoots a₁ P, sliceNormal R a a₁ k = 0 → 0 < sliceOffset ξ k then
        weight (sliceNormal R a a₁ (P := P)) param (repBasis D hm hS hP hSP) else 0 := by
  unfold vertexSum
  rw [Finset.sum_eq_single (repBasis D hm hS hP hSP)]
  · simp only [repBasis_feasible_iff D hm hS hP hSP]
  · intro J _ hJ
    split_ifs with hf
    · exact (hJ (eq_repBasis_of_feasible D hm hS hP hSP J hf)).elim
    · rfl
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The representatives correspond to the coarse simple roots. -/
def repSimpleEquiv : repSet R a a₁ P ≃ simpleRoots a S :=
  Equiv.ofBijective
    (fun i => ⟨⟨((sliceNormal R a a₁ (i : simpleRoots a₁ P) : noncentral R a) : E),
        (sliceNormal R a a₁ (i : simpleRoots a₁ P)).prop.1⟩,
      value_mem_simpleRoots D hm hS hP hSP
        (mem_sliceValues_iff.mpr ⟨(mem_repSet.mp i.prop).1, (i : simpleRoots a₁ P), rfl⟩)⟩)
    ⟨fun i j h => by
        apply (repValueEquiv R a a₁ P).injective
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun x : simpleRoots a S => ((x : a) : E)) h
        exact this,
      fun b => by
        obtain ⟨c, hc, hcb⟩ := exists_value_of_mem_simpleRoots D hS hP hSP b.prop
        refine ⟨(repValueEquiv R a a₁ P).symm ⟨c, hc⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        change ((sliceNormal R a a₁ ((repValueEquiv R a a₁ P).symm ⟨c, hc⟩ : simpleRoots a₁ P) :
          noncentral R a) : E) = ((b : a) : E)
        rw [← repValueEquiv_apply, Equiv.apply_symm_apply]
        exact hcb⟩

theorem coe_repSimpleEquiv (i : repSet R a a₁ P) :
    ((repSimpleEquiv D hm hS hP hSP i : a) : E) =
      ((sliceNormal R a a₁ (i : simpleRoots a₁ P) : noncentral R a) : E) := rfl

/-- The weight of the representative basis is the reciprocal coarse denominator. -/
theorem weight_repBasis (Λ : StrongDual ℝ a) :
    weight (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (repBasis D hm hS hP hSP) =
      (theta a S Λ)⁻¹ := by
  rw [theta_inv_eq_gram_div]
  let e := repSimpleEquiv D hm hS hP hSP
  have hv : gramVolume (fun i : (repBasis D hm hS hP hSP).val =>
        sliceNormal R a a₁ (i : simpleRoots a₁ P)) =
      gramVolume (fun j : simpleRoots a S => ((j : a) : E)) := by
    rw [← gramVolume_subtype (noncentral R a), ← gramVolume_reindex e]
    rfl
  have hp : (∏ i ∈ (repBasis D hm hS hP hSP).val, sliceParameter R Λ (sliceNormal R a a₁ i)) =
      ∏ j : simpleRoots a S, (Complex.I * (Λ (j : a) : ℂ)) := by
    rw [← Finset.prod_coe_sort]
    apply Fintype.prod_equiv e
    intro i
    change Complex.I * (Λ (Submodule.inclusion inf_le_left
      (sliceNormal R a a₁ (i : simpleRoots a₁ P))) : ℂ) = _
    rfl
  unfold weight
  rw [hv, hp]

/-- **The vertex sum of a fine chamber over a coarse chamber.** For a special coarse subspace,
the weighted vertex sum of the affine slice of a fine chamber whose closure contains a coarse
chamber is the reciprocal coarse denominator when every constant inequality is strict, and `0`
otherwise. -/
theorem vertexSum_eq_of_special_extension (Λ : StrongDual ℝ a)
    (hΛ : ∀ r ∈ R, restrictedRoot a r ≠ 0 → Λ (restrictedRoot a r) ≠ 0) :
    vertexSum (sliceNormal R a a₁ (P := P)) (sliceParameter R Λ) (sliceOffset ξ) =
      if isSliceLift R a a₁ ξ S P then (theta a S Λ)⁻¹ else 0 := by
  have hkeep (A : WallIndex (sliceNormal R a a₁ (P := P)))
      (hA : sliceNormal R a a₁ (A.2 : simpleRoots a₁ P) = 0) :
      0 < sliceOffset ξ (A.2 : simpleRoots a₁ P) *
        repOffset R a a₁ ξ (A.2 : simpleRoots a₁ P) := by
    rw [repOffset_of_zero hA]
    have h := CentralSubspaceDescent.sliceOffset_regular D hP A
    change A.1.slack A.2 (sliceOffset ξ) ≠ 0 at h
    rw [slack_of_normal_eq_zero A.1 hA] at h
    exact mul_self_pos.mpr h
  rw [vertexSum_eq_of_regular (sliceParameter R Λ) (CentralSubspaceDescent.sliceParameter_ne_zero D hP Λ hΛ)
    (CentralSubspaceDescent.sliceOffset_regular D hP) (repOffset_regular D hm hS hP hSP) hkeep,
    vertexSum_repOffset D hm hS hP hSP, weight_repBasis D hm hS hP hSP]
  simp only [isSliceLift, hSP, true_and]

end VertexSum

end SpecialSlice

end Langlands.GMFamily
