import Langlands.GroupScheme.Rational.TorusLinearization.Complement

/-! # A stable subspace of additive polynomials that generates and has independent linear parts -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization

section Spans

variable {n : ℕ} {k : Type u} [Field k] {p : ℕ}

theorem subset_frobSpan_zero (S : Set (MvPolynomial (Fin n) k)) :
    S ⊆ frobSpan k p 0 S := fun g hg => by
  simpa using pow_mem_frobSpan (p := p) hg (le_refl 0)

theorem frobSpan_le_frobSpan_zero (m : ℕ) (S : Set (MvPolynomial (Fin n) k)) :
    frobSpan k p m S ≤ frobSpan k p 0 S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, r, -, rfl⟩
  exact pow_mem_frobSpan hg (Nat.zero_le r)

variable (K : Type u) [Field K] [Algebra k K]

/-- The `K`-span of the image of a `k`-subspace of polynomials. -/
abbrev spanK (W : Submodule k (MvPolynomial (Fin n) k)) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (MvPolynomial.map (algebraMap k K) '' (W : Set (MvPolynomial (Fin n) k)))

variable {K}

theorem map_mem_spanK {W : Submodule k (MvPolynomial (Fin n) k)} {f : MvPolynomial (Fin n) k}
    (hf : f ∈ W) : MvPolynomial.map (algebraMap k K) f ∈ spanK K W :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem spanK_mono {W W' : Submodule k (MvPolynomial (Fin n) k)} (h : W ≤ W') :
    spanK K W ≤ spanK K W' :=
  Submodule.span_mono (Set.image_mono (SetLike.coe_mono h))

variable [hp : Fact p.Prime] [CharP k p]

/-- The `p`-th power carries the `K`-span of `W` into the `K`-span of `W'` when it carries `W`
into `W'`. -/
theorem pow_mem_spanK {W W' : Submodule k (MvPolynomial (Fin n) k)}
    (hW : ∀ f ∈ W, f ^ p ∈ W') {v : MvPolynomial (Fin n) K} (hv : v ∈ spanK K W) :
    v ^ p ∈ spanK K W' := by
  have h0 : (p : MvPolynomial (Fin n) K) = 0 := natCast_eq_zero_of_algebra k _
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [← map_pow]
    exact map_mem_spanK (hW w hw)
  | zero => rw [zero_pow hp.out.ne_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    have := add_pow_prime_pow_of_natCast_eq_zero p h0 x y 1
    rw [pow_one] at this
    rw [this]
    exact add_mem hx hy
  | smul c x _ hx => rw [smul_pow]; exact Submodule.smul_mem _ _ hx

omit hp [CharP k p] in
theorem map_mem_addSpan {f : MvPolynomial (Fin n) k} (hf : f ∈ addSpan n k p) :
    MvPolynomial.map (algebraMap k K) f ∈ addSpan n K p :=
  show (↑(MvPolynomial.map (algebraMap k K) f).support : Set _) ⊆ addExponents n p from
    fun _ hm => (show (↑f.support : Set _) ⊆ addExponents n p from hf)
      (support_map_subset _ f hm)

omit hp [CharP k p] in
/-- An additive polynomial without linear terms is a higher additive polynomial. -/
theorem mem_higher_of_coeff_eq_zero {f : MvPolynomial (Fin n) k} (hf : f ∈ addSpan n k p)
    (h1 : ∀ j, f.coeff (Finsupp.single j 1) = 0) : f ∈ higher n k p := by
  classical
  rw [f.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨j, r, rfl⟩ := (show (↑f.support : Set _) ⊆ addExponents n p from hf) hm
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact absurd (h1 j) (by simpa [mem_support_iff] using hm)
  · rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (pow_mem_frobSpan ⟨j, rfl⟩ hr)

end Spans

namespace PointAction

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {I : Type u} {n : ℕ}
  (a : PointAction k K I n) (p : ℕ) [hp : Fact p.Prime] [CharP k p]

omit hp [CharP k p] in
theorem stable_of_le_fixed {W : Submodule k (MvPolynomial (Fin n) k)} (hW : W ≤ a.fixed p) :
    a.Stable W := fun B _ _ t w hw => by
  rw [(hW hw).2 B t]
  exact Submodule.subset_span ⟨w, hw, rfl⟩

theorem isAddPoly_of_mem_fixed {f : MvPolynomial (Fin n) k} (hf : f ∈ a.fixed p) :
    IsAddPoly f :=
  addSpan_le_addPolys (natCast_eq_zero_of_algebra k _) hf.1

theorem pow_mem_fixed {f : MvPolynomial (Fin n) k} (hf : f ∈ a.fixed p) : f ^ p ∈ a.fixed p := by
  refine ⟨?_, fun B _ _ t => by rw [map_pow, hf.2 B t, map_pow]⟩
  have h := pow_mem_of_mem_addSpan (r := 1) (natCast_eq_zero_of_algebra k k)
    (fun l s _ => X_pow_mem_addSpan l s) hf.1
  rwa [pow_one] at h

/-- A Frobenius basis of the fixed polynomials. -/
theorem exists_frobBasis_fixed : ∃ G : Finset (MvPolynomial (Fin n) k),
    (G : Set (MvPolynomial (Fin n) k)) ⊆ a.fixed p ∧
      a.fixed p ≤ frobSpan k p 0 (G : Set (MvPolynomial (Fin n) k)) ∧ FrobIndep G :=
  exists_frobBasis Finset.univ (a.fixed p) (fun _ hf => a.isAddPoly_of_mem_fixed p hf)
    (fun _ hf => a.pow_mem_fixed p hf) (fun _ _ j hj => absurd (Finset.mem_univ j) hj)

section Graded

variable [Fintype I] [DecidableEq I]

/-- Purity: a fixed polynomial without linear terms is a combination of `p`-th powers of
Frobenius powers of a Frobenius basis of the fixed polynomials. -/
theorem mem_frobSpan_one_of_mem_higher {G : Finset (MvPolynomial (Fin n) k)}
    (hfG : a.fixed p ≤ frobSpan k p 0 (G : Set (MvPolynomial (Fin n) k)))
    {f : MvPolynomial (Fin n) k} (hh : f ∈ higher n k p) (hf : f ∈ a.fixed p) :
    f ∈ frobSpan k p 1 (G : Set (MvPolynomial (Fin n) k)) := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have key : ∀ y ∈ higher n k p, a.comp 0 (MvPolynomial.map (algebraMap k K) y) ∈
      spanK K (frobSpan k p 1 (G : Set (MvPolynomial (Fin n) k))) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨j, rfl⟩, r, hr, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hr
      rw [pow_succ, pow_mul, map_pow (MvPolynomial.map (algebraMap k K)) (X j ^ p ^ r) p,
        show (0 : I → ℤ) = p • 0 from (smul_zero _).symm, a.comp_pow_char_smul p]
      refine pow_mem_spanK (fun g hg => pow_mem_frobSpan_succ hg) (spanK_mono hfG ?_)
      have hadd := a.comp_mem_addSpan p 0
        (map_mem_addSpan (K := K) (X_pow_mem_addSpan (A := k) j r))
      refine a.mem_span_fixed p hadd fun ψ hψ => ?_
      rw [a.comp_comp]
      split_ifs with h
      exacts [absurd h (Ne.symm hψ), rfl]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul_eq, map_smul]; exact Submodule.smul_mem _ _ hx
  refine mem_of_map_mem_span (K := K) ?_
  have hs : (a.coact (MvPolynomial.map (algebraMap k K) f)).coeff.support ⊆ {0} := by
    intro χ hχ
    rw [Finset.mem_singleton]
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hχ) (a.comp_map_fixed p hne hf)
  have hsum := a.sum_comp (MvPolynomial.map (algebraMap k K) f) hs
  rw [Finset.sum_singleton] at hsum
  rw [← hsum]
  exact key f hh

/-- Graded Nakayama: a `k`-subspace closed under `p`-th powers that contains the complement and
the fixed polynomials contains the components of every additive polynomial. -/
theorem comp_map_mem_spanK (θ : K →ₗ[k] k) (hθ : θ 1 = 1)
    (π' : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K)
    (hπ1 : ∀ y ∈ spanK K (a.fixHigher p), π' y = y) (hπ2 : ∀ v, π' v ∈ spanK K (a.fixHigher p))
    (hπ3 : ∀ χ v, π' (a.comp χ v) = a.comp χ (π' v))
    {F : Submodule k (MvPolynomial (Fin n) k)} (hF1 : complement p θ π' ≤ F)
    (hF2 : a.fixed p ≤ F) (hFp : ∀ f ∈ F, f ^ p ∈ F) (χ : I → ℤ) {f : MvPolynomial (Fin n) k}
    (hf : f ∈ addSpan n k p) : a.comp χ (MvPolynomial.map (algebraMap k K) f) ∈ spanK K F := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  suffices h : ∀ N (χ : I → ℤ), ∑ i, (χ i).natAbs = N → ∀ f ∈ addSpan n k p,
      a.comp χ (MvPolynomial.map (algebraMap k K) f) ∈ spanK K F from h _ χ rfl f hf
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro χ hN f hf
  by_cases hχ : χ = 0
  · subst hχ
    have h1 := a.comp_mem_addSpan p 0 (map_mem_addSpan (K := K) hf)
    refine spanK_mono hF2 (a.mem_span_fixed p h1 fun ψ hψ => ?_)
    rw [a.comp_comp]
    split_ifs with h
    exacts [absurd h (Ne.symm hψ), rfl]
  obtain ⟨l, hl, y, hy, rfl⟩ :=
    Submodule.mem_sup.mp (a.addSpan_le_complement_sup p θ π' hθ hπ1 hπ2 hf)
  have hhigher : ∀ y ∈ higher n k p,
      a.comp χ (MvPolynomial.map (algebraMap k K) y) ∈ spanK K F := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨j, rfl⟩, r, hr, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hr
      rw [pow_succ, pow_mul, map_pow (MvPolynomial.map (algebraMap k K)) (X j ^ p ^ r) p,
        a.comp_pow_char p]
      refine Submodule.sum_mem _ fun ψ _ => ?_
      split_ifs with hψ
      · have hsum : ∑ i, (χ i).natAbs = p * ∑ i, (ψ i).natAbs := by
          rw [← hψ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Int.natAbs_mul]
        have hψ0 : ψ ≠ 0 := by
          rintro rfl
          exact hχ (by rw [← hψ, smul_zero])
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hψ0
        have hpos : 0 < ∑ i, (ψ i).natAbs :=
          lt_of_lt_of_le (Int.natAbs_pos.mpr hi)
            (Finset.single_le_sum (f := fun i => (ψ i).natAbs) (fun i _ => Nat.zero_le _)
              (Finset.mem_univ i))
        have hlt : ∑ i, (ψ i).natAbs < N := by
          rw [← hN, hsum]
          nlinarith [hp.out.two_le]
        exact pow_mem_spanK hFp (ih _ hlt ψ rfl _ (X_pow_mem_addSpan j r))
      · exact zero_mem _
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul_eq, map_smul]; exact Submodule.smul_mem _ _ hx
  obtain ⟨y, hy', z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add, map_add, map_add]
  refine add_mem (spanK_mono hF1 (a.comp_mem_span_of_stable
    (a.stable_complement p θ π' hθ hπ1 hπ2 hπ3) χ (map_mem_spanK hl))) (add_mem ?_ ?_)
  · exact hhigher y hy'
  · rw [a.comp_map_fixed p hχ hz]
    exact zero_mem _

/-- Every additive polynomial lies in a `k`-subspace closed under `p`-th powers that contains
the complement and the fixed polynomials. -/
theorem addSpan_le_of_frobClosed (θ : K →ₗ[k] k) (hθ : θ 1 = 1)
    (π' : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K)
    (hπ1 : ∀ y ∈ spanK K (a.fixHigher p), π' y = y) (hπ2 : ∀ v, π' v ∈ spanK K (a.fixHigher p))
    (hπ3 : ∀ χ v, π' (a.comp χ v) = a.comp χ (π' v))
    {F : Submodule k (MvPolynomial (Fin n) k)} (hF1 : complement p θ π' ≤ F)
    (hF2 : a.fixed p ≤ F) (hFp : ∀ f ∈ F, f ^ p ∈ F) : addSpan n k p ≤ F := by
  intro f hf
  refine mem_of_map_mem_span (K := K) ?_
  rw [← a.sum_comp (MvPolynomial.map (algebraMap k K) f) subset_rfl]
  exact Submodule.sum_mem _ fun χ _ =>
    a.comp_map_mem_spanK p θ hθ π' hπ1 hπ2 hπ3 hF1 hF2 hFp χ hf

/-- A stable subspace of additive polynomials on which the linear terms are injective and whose
Frobenius span contains the variables: the complement plus the span of a Frobenius basis of the
fixed polynomials. -/
theorem exists_subspace : ∃ W : Submodule k (MvPolynomial (Fin n) k), W ≤ addSpan n k p ∧
    a.Stable W ∧
    (∀ w ∈ W, (∀ j, w.coeff (Finsupp.single j 1) = 0) → w = 0) ∧
    ∀ j, (X j : MvPolynomial (Fin n) k) ∈ frobSpan k p 0 (W : Set (MvPolynomial (Fin n) k)) := by
  obtain ⟨θ, hθ⟩ := exists_theta k K
  obtain ⟨π', hπ1, hπ2, hπ3⟩ := a.exists_projection p
  obtain ⟨G, hGf, hfG, hGi⟩ := a.exists_frobBasis_fixed p
  have hGW : Submodule.span k (G : Set (MvPolynomial (Fin n) k)) ≤ a.fixed p :=
    Submodule.span_le.mpr hGf
  refine ⟨complement p θ π' ⊔ Submodule.span k (G : Set _), ?_, ?_, ?_, ?_⟩
  · exact sup_le (fun _ hf => (Submodule.mem_inf.mp hf).2) (hGW.trans fun _ hf => hf.1)
  · exact Stable.sup a (a.stable_complement p θ π' hθ hπ1 hπ2 hπ3) (a.stable_of_le_fixed p hGW)
  · intro w hw h1
    obtain ⟨l, hl, g, hg, rfl⟩ := Submodule.mem_sup.mp hw
    have hh := mem_higher_of_coeff_eq_zero (add_mem (Submodule.mem_inf.mp hl).2 (hGW hg).1) h1
    have hlf : l ∈ a.fixHigher p := by
      rw [← add_sub_cancel_right l g]
      exact sub_mem (Submodule.mem_sup_left hh) (Submodule.mem_sup_right (hGW hg))
    have hl0 : l = 0 := by
      rw [← Submodule.mem_bot k, ← a.complement_inf_fixHigher p θ π' hθ hπ1]
      exact Submodule.mem_inf.mpr ⟨hl, hlf⟩
    subst hl0
    rw [zero_add] at hh ⊢
    have hg1 := a.mem_frobSpan_one_of_mem_higher p hfG hh (hGW hg)
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hg
    rw [← hc] at hg1 ⊢
    exact Finset.sum_eq_zero fun x hx => by rw [hGi.eq_zero_of_sum_smul_mem c hg1 x hx, zero_smul]
  · intro j
    have hGW' : (G : Set (MvPolynomial (Fin n) k)) ⊆
        (complement p θ π' ⊔ Submodule.span k (G : Set _) : Submodule k _) :=
      fun g hg => Submodule.mem_sup_right (Submodule.subset_span hg)
    refine a.addSpan_le_of_frobClosed p θ hθ π' hπ1 hπ2 hπ3
      (fun f hf => subset_frobSpan_zero _ (Submodule.mem_sup_left hf))
      (hfG.trans (frobSpan_mono hGW'))
      (fun f hf => frobSpan_le_frobSpan_zero 1 _ (pow_mem_frobSpan_succ hf)) ?_
    simpa using X_pow_mem_addSpan (A := k) (p := p) j 0

end Graded

end PointAction

end Langlands.GroupScheme.TorusLinearization
