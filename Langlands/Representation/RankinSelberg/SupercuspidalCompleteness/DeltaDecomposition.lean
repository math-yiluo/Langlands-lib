import Langlands.Representation.RankinSelberg.SupercuspidalCompleteness.DeltaFunctions

/-!
# Finite delta decompositions in compact induction from a character

A right `K`-invariant vector of `c-Ind_N^G θ`, with `K` a compact open subgroup, is a finite
linear combination of delta functions.
-/

noncomputable section

namespace Langlands.RankinSelberg.SupercuspidalCompleteness

open MeasureTheory QuotientIntegration Induction Whittaker.CompletenessPairing

universe uG

section Decomposition

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} {θ : N →* ℂˣ}

/-- A nonzero value of a right `K`-invariant covariant function forces goodness. -/
theorem isGood_of_eval_ne_zero {K : Subgroup G}
    (x : CompactFunctions N (characterRepresentation θ))
    (hx : ∀ y, ∀ k ∈ K, eval _ _ x.1 (y * k) = eval _ _ x.1 y) {c : G}
    (hc : eval _ _ x.1 c ≠ 0) : IsGood N θ K c := by
  intro n hn
  have h1 : eval _ _ x.1 ((n : G) * c) = (θ n : ℂ) * eval _ _ x.1 c := by
    have := x.1.1.property n c
    change eval _ _ x.1 ((n : G) * c) = (θ n : ℂ) • eval _ _ x.1 c at this
    rw [this, smul_eq_mul]
  have h2 : eval _ _ x.1 ((n : G) * c) = eval _ _ x.1 c := by
    have : (n : G) * c = c * (c⁻¹ * (n : G) * c) := by group
    rw [this, hx c _ hn]
  rw [h2] at h1
  have h3 : ((θ n : ℂ) - 1) * eval _ _ x.1 c = 0 := by rw [sub_mul, ← h1]; ring
  rcases mul_eq_zero.mp h3 with h | h
  · exact Units.ext (sub_eq_zero.mp h)
  · exact absurd h hc

/-- The orbit data for the support of a compactly supported right `K`-invariant function. -/
theorem exists_finset_orbits {K : Subgroup G} (hK : IsOpen (K : Set G))
    (x : CompactFunctions N (characterRepresentation θ)) :
    ∃ s : Finset G, Set.InjOn (orbit N K) (s : Set G) ∧
      ∀ y, eval _ _ x.1 y ≠ 0 → ∃ c ∈ s, (Quotient.mk _ y : QuotientIntegration.LeftQuotient N) ∈ orbit N K c := by
  classical
  have hcomp : IsCompact (quotientSupport N (eval _ _ x.1)) := x.2
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover
    (fun c : quotientSupport N (eval _ _ x.1) => orbit N K (Quotient.out c.val))
    (fun c => isOpen_orbit N hK _) (by
      intro q hq
      refine Set.mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩
      have h := mk_mem_orbit N K (Quotient.out q)
      rwa [Quotient.out_eq] at h)
  let t' : Finset G := t.image (fun c => Quotient.out c.val)
  obtain ⟨s, hst, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (f := orbit N K) (t' : Set G) (t'.image (orbit N K)) (by
      intro S hS
      simpa using hS)
  refine ⟨s, hinj, ?_⟩
  intro y hy
  have hq : (Quotient.mk _ y : QuotientIntegration.LeftQuotient N) ∈ quotientSupport N (eval _ _ x.1) :=
    ⟨y, hy, rfl⟩
  obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.mp (ht hq)
  have hmem : orbit N K (Quotient.out i.val) ∈ s.image (orbit N K) := by
    rw [himg]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_image_of_mem _ hit, rfl⟩
  obtain ⟨c, hcs, hc⟩ := Finset.mem_image.mp hmem
  exact ⟨c, hcs, hc ▸ hi⟩

/-- The delta vector at `c` if `c` is good, and zero otherwise. -/
def deltaVector' (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (c : G) :
    CompactFunctions N (characterRepresentation θ) := by
  classical
  exact if h : IsGood N θ K c then deltaVector K hK c h else 0

theorem deltaVector'_of_good {K : OpenSubgroup G} {hK : IsCompact (K : Set G)} {c : G}
    (h : IsGood N θ K c) : deltaVector' (N := N) (θ := θ) K hK c = deltaVector K hK c h := by
  classical
  unfold deltaVector'
  rw [dif_pos h]

/-- A right `K`-invariant vector is a finite combination of delta vectors. -/
theorem exists_delta_decomposition (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x : CompactFunctions N (characterRepresentation θ))
    (hx : ∀ y, ∀ k ∈ (K : Subgroup G), eval _ _ x.1 (y * k) = eval _ _ x.1 y) :
    ∃ s : Finset G, (∀ c ∈ s, eval _ _ x.1 c ≠ 0 → IsGood N θ K c) ∧
      x = ∑ c ∈ s, eval _ _ x.1 c • deltaVector' K hK c := by
  classical
  obtain ⟨s, hinj, hcov⟩ := exists_finset_orbits (N := N) (θ := θ) K.isOpen x
  have hgood : ∀ c, eval _ _ x.1 c ≠ 0 → IsGood N θ K c := fun c hc =>
    isGood_of_eval_ne_zero x hx hc
  refine ⟨s, fun c _ hc => hgood c hc, ?_⟩
  -- the covariance of `x`
  have hcov' : ∀ (n : N) (y : G), eval _ _ x.1 ((n : G) * y) = (θ n : ℂ) * eval _ _ x.1 y := by
    intro n y
    have := x.1.1.property n y
    change eval _ _ x.1 ((n : G) * y) = (θ n : ℂ) • eval _ _ x.1 y at this
    rw [this, smul_eq_mul]
  -- the term at `c` evaluated at `y`
  have hterm : ∀ c y, eval _ _ (eval _ _ x.1 c • deltaVector' (N := N) (θ := θ) K hK c).1 y =
      if eval _ _ x.1 c = 0 then 0 else eval _ _ x.1 c * deltaFun N θ K c y := by
    intro c y
    by_cases hc : eval _ _ x.1 c = 0
    · rw [if_pos hc, eval_smul, hc, zero_smul]
    · rw [if_neg hc, eval_smul, deltaVector'_of_good (hgood c hc), eval_deltaVector, smul_eq_mul]
  apply compactFunctions_ext
  intro y
  rw [eval_sum]
  by_cases hy : eval _ _ x.1 y = 0
  · rw [hy]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [hterm]
    split_ifs with hc
    · rfl
    · by_cases hyc : ∃ n : N, ∃ k ∈ (K : Subgroup G), y = (n : G) * (c * k)
      · obtain ⟨n, k, hk, rfl⟩ := hyc
        exfalso
        apply hc
        have h1 := hcov' n (c * k)
        rw [hy, hx c k hk] at h1
        have hθ : (θ n : ℂ) ≠ 0 := Units.ne_zero _
        exact (mul_eq_zero.mp h1.symm).resolve_left hθ
      · rw [deltaFun_eq_zero hyc, mul_zero]
  · obtain ⟨c, hcs, hyc⟩ := hcov y hy
    obtain ⟨k, hk⟩ := hyc
    have hn : y * (c * k.val)⁻¹ ∈ N := QuotientGroup.rightRel_apply.mp (Quotient.exact hk)
    set n : N := ⟨y * (c * k.val)⁻¹, hn⟩
    have hyeq : y = (n : G) * (c * k.val) := by simp only [n]; group
    have hxy : eval _ _ x.1 y = (θ n : ℂ) * eval _ _ x.1 c := by
      rw [hyeq, hcov', hx c k.val k.property]
    have hxc : eval _ _ x.1 c ≠ 0 := by
      intro h0
      apply hy
      rw [hxy, h0, mul_zero]
    rw [Finset.sum_eq_single c]
    · rw [hterm, if_neg hxc, hyeq, deltaFun_apply (hgood c hxc) n k.property, ← hyeq, hxy,
        mul_comm]
    · intro c' hc's hc'c
      rw [hterm]
      split_ifs with h0
      · rfl
      · have hyc' : ¬ ∃ n : N, ∃ k ∈ (K : Subgroup G), y = (n : G) * (c' * k) := by
          rintro ⟨n', k', hk', he⟩
          apply hc'c
          apply hinj hc's hcs
          have h1 : (Quotient.mk _ y : QuotientIntegration.LeftQuotient N) ∈ orbit N K c' := by
            refine ⟨⟨k', hk'⟩, ?_⟩
            apply Quotient.sound
            change QuotientGroup.rightRel _ (c' * k') y
            rw [QuotientGroup.rightRel_apply, he]
            simpa [mul_assoc] using n'.property
          have h2 : (Quotient.mk _ y : QuotientIntegration.LeftQuotient N) ∈ orbit N K c :=
            ⟨k, hk⟩
          exact (orbit_eq_of_mk_mem h1).symm.trans (orbit_eq_of_mk_mem h2)
        rw [deltaFun_eq_zero hyc', mul_zero]
    · intro h
      exact absurd hcs h

end Decomposition

end Langlands.RankinSelberg.SupercuspidalCompleteness
