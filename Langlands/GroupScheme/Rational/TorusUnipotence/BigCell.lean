import Langlands.GroupScheme.Rational.TorusUnipotence.BigCellStatement
import Langlands.GroupScheme.Rational.TorusUnipotence.TruncatedSection
import Mathlib.RingTheory.Filtration

/-! # Graded big-cell injectivity -/

noncomputable section

universe u v w

open MvPolynomial TensorProduct

namespace Langlands.GroupScheme.TorusUnipotence

section Keep

variable {k : Type u} [CommRing k] {σ : Type w}

/-- The substitution which keeps the variables satisfying `P` and sends the others to zero. -/
def keepVars (P : σ → Prop) [DecidablePred P] : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun s => if P s then X s else 0

variable (P : σ → Prop) [DecidablePred P]

theorem keepVars_X (s : σ) : keepVars (k := k) P (X s) = if P s then X s else 0 :=
  aeval_X _ s

/-- A polynomial each of whose monomials involves a variable outside `P` is killed. -/
theorem keepVars_eq_zero {p : MvPolynomial σ k}
    (hp : ∀ m ∈ p.support, ∃ s, m s ≠ 0 ∧ ¬ P s) : keepVars P p = 0 := by
  classical
  rw [p.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨s, hms, hPs⟩ := hp m hm
  rw [keepVars, aeval_monomial, Finsupp.prod,
    Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hms) (by simp [hPs, hms]), mul_zero]

/-- The substitution preserves the ideal of the variables. -/
theorem keepVars_mem_idealOfVars {p : MvPolynomial σ k} (hp : p ∈ idealOfVars σ k) :
    keepVars P p ∈ idealOfVars σ k := by
  have h : idealOfVars σ k ≤ (idealOfVars σ k).comap (keepVars P) := by
    refine (Ideal.span_le (I := (idealOfVars σ k).comap (keepVars P))).2 ?_
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, keepVars_X]
    split_ifs
    · exact Ideal.subset_span ⟨s, rfl⟩
    · exact Ideal.zero_mem _
  exact h hp

theorem keepVars_pow_le_comap (N : ℕ) :
    idealOfVars σ k ^ N ≤ (idealOfVars σ k ^ N).comap (keepVars P) :=
  (Ideal.pow_right_mono (fun _ hp => keepVars_mem_idealOfVars P hp) N).trans
    (Ideal.le_comap_pow _ N)

/-- The substitution `keepVars P` on a truncated polynomial ring. -/
def truncKeep (N : ℕ) :
    (MvPolynomial σ k ⧸ idealOfVars σ k ^ N) →ₐ[k] MvPolynomial σ k ⧸ idealOfVars σ k ^ N :=
  Ideal.Quotient.liftₐ (idealOfVars σ k ^ N)
    ((Ideal.Quotient.mkₐ k (idealOfVars σ k ^ N)).comp (keepVars P)) fun a ha => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact keepVars_pow_le_comap P N ha

theorem truncKeep_mk (N : ℕ) (p : MvPolynomial σ k) :
    truncKeep P N (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (keepVars P p) :=
  rfl

theorem truncKeep_mem {N : ℕ} {y : MvPolynomial σ k ⧸ idealOfVars σ k ^ N}
    (hy : y ∈ truncVarIdeal σ k N) : truncKeep P N y ∈ truncVarIdeal σ k N := by
  obtain ⟨p, hp, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  rw [truncKeep_mk]
  exact Ideal.mem_map_of_mem _ (keepVars_mem_idealOfVars P hp)

/-- A nonzero exponent vector of nonpositive weight involves a variable of nonpositive
weight. -/
theorem exists_not_pos_of_weight_nonpos {w : σ → ℤ} {m : σ →₀ ℕ} (hm : m ≠ 0)
    (h : Finsupp.weight w m ≤ 0) : ∃ s, m s ≠ 0 ∧ ¬ 0 < w s := by
  by_contra hcon
  push Not at hcon
  have hpos : (0 : ℤ) < Finsupp.weight w m := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    calc (0 : ℤ) = ∑ s ∈ m.support, (0 : ℤ) := by simp
      _ < ∑ s ∈ m.support, m s • w s := by
        refine Finset.sum_lt_sum_of_nonempty (Finsupp.support_nonempty_iff.2 hm) fun s hs => ?_
        have hs' := Finsupp.mem_support_iff.1 hs
        rw [nsmul_eq_mul]
        exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs') (hcon s hs')
  omega

/-- A nonzero exponent vector of nonnegative weight involves a variable of nonnegative
weight. -/
theorem exists_not_neg_of_weight_nonneg {w : σ → ℤ} {m : σ →₀ ℕ} (hm : m ≠ 0)
    (h : 0 ≤ Finsupp.weight w m) : ∃ s, m s ≠ 0 ∧ ¬ w s < 0 := by
  by_contra hcon
  push Not at hcon
  have hneg : Finsupp.weight w m < 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    calc ∑ s ∈ m.support, m s • w s < ∑ s ∈ m.support, (0 : ℤ) := by
          refine Finset.sum_lt_sum_of_nonempty (Finsupp.support_nonempty_iff.2 hm)
            fun s hs => ?_
          have hs' := Finsupp.mem_support_iff.1 hs
          rw [nsmul_eq_mul]
          exact mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero hs') (hcon s hs')
      _ = 0 := by simp
  omega

theorem ne_zero_of_mem_support_of_constantCoeff {p : MvPolynomial σ k}
    (hc : constantCoeff p = 0) {m : σ →₀ ℕ} (hm : m ∈ p.support) : m ≠ 0 := by
  rintro rfl
  exact mem_support_iff.1 hm (by simpa [constantCoeff_eq] using hc)

/-- Keeping only the positive-weight variables kills a weighted-homogeneous polynomial of
nonpositive degree without constant term. -/
theorem keepVars_pos_eq_zero {w : σ → ℤ} {p : MvPolynomial σ k} {d : ℤ}
    (hp : IsWeightedHomogeneous w p d) (hd : d ≤ 0) (hc : constantCoeff p = 0) :
    keepVars (fun s => 0 < w s) p = 0 :=
  keepVars_eq_zero _ fun m hm => exists_not_pos_of_weight_nonpos
    (ne_zero_of_mem_support_of_constantCoeff hc hm) (by rw [hp (mem_support_iff.1 hm)]; exact hd)

/-- Keeping only the negative-weight variables kills a weighted-homogeneous polynomial of
nonnegative degree without constant term. -/
theorem keepVars_neg_eq_zero {w : σ → ℤ} {p : MvPolynomial σ k} {d : ℤ}
    (hp : IsWeightedHomogeneous w p d) (hd : 0 ≤ d) (hc : constantCoeff p = 0) :
    keepVars (fun s => w s < 0) p = 0 :=
  keepVars_eq_zero _ fun m hm => exists_not_neg_of_weight_nonneg
    (ne_zero_of_mem_support_of_constantCoeff hc hm) (by rw [hp (mem_support_iff.1 hm)]; exact hd)

end Keep

section Main

variable {k : Type u} {A : Type u} [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k)

/-- For two maps which agree with the augmentation modulo an ideal `J`, the product map on a
tensor differs from the sum of the two counit contractions by an element of `J ^ 2`. -/
theorem productMap_sub_mem_sq {B : Type*} [CommRing B] [Algebra k B] (J : Ideal B)
    (f g : A →ₐ[k] B) (hf : ∀ x, f x - algebraMap k B (ε x) ∈ J)
    (hg : ∀ x, g x - algebraMap k B (ε x) ∈ J) (t : A ⊗[k] A) :
    Algebra.TensorProduct.productMap f g t
      - f (Algebra.TensorProduct.rid k k A (Algebra.TensorProduct.map (AlgHom.id k A) ε t))
      - g (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map ε (AlgHom.id k A) t))
      + algebraMap k B (ε (Algebra.TensorProduct.rid k k A
          (Algebra.TensorProduct.map (AlgHom.id k A) ε t))) ∈ J ^ 2 := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have h : Algebra.TensorProduct.productMap f g (x ⊗ₜ y)
        - f (Algebra.TensorProduct.rid k k A
          (Algebra.TensorProduct.map (AlgHom.id k A) ε (x ⊗ₜ y)))
        - g (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map ε (AlgHom.id k A) (x ⊗ₜ y)))
        + algebraMap k B (ε (Algebra.TensorProduct.rid k k A
            (Algebra.TensorProduct.map (AlgHom.id k A) ε (x ⊗ₜ y)))) =
        (f x - algebraMap k B (ε x)) * (g y - algebraMap k B (ε y)) := by
      simp only [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.rid_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply,
        Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    rw [h, pow_two]
    exact Ideal.mul_mem_mul (hf x) (hg y)
  | add t₁ t₂ h₁ h₂ =>
    have := Ideal.add_mem _ h₁ h₂
    convert this using 1
    simp only [map_add]
    ring

variable {σ : Type w} (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- The kernel of the big-cell map lies in every power of the augmentation ideal. -/
theorem mem_pow_of_bigCellMap_eq_zero [Algebra.FormallySmooth k A] (Δ : A →ₐ[k] A ⊗[k] A)
    (hε : ∀ d : ℤ, d ≠ 0 → ∀ a ∈ 𝒜 d, ε a = 0)
    (hl : ∀ x, Algebra.TensorProduct.lid k A
      (Algebra.TensorProduct.map ε (AlgHom.id k A) (Δ x)) = x)
    (hr : ∀ x, Algebra.TensorProduct.rid k k A
      (Algebra.TensorProduct.map (AlgHom.id k A) ε (Δ x)) = x)
    (b : Module.Basis σ k (RingHom.ker ε).Cotangent) (z : σ → A) (w : σ → ℤ)
    (hw : ∀ s, w s ≠ 0) (hzw : ∀ s, z s ∈ 𝒜 (w s)) (hzb : ∀ s, cotangentMap ε (z s) = b s)
    {N : ℕ} (hN : N ≠ 0) {a : A} (ha : bigCellMap 𝒜 ε Δ a = 0) :
    a ∈ RingHom.ker ε ^ N := by
  have hz : ∀ s, ε (z s) = 0 := fun s => hε _ (hw s) _ (hzw s)
  obtain ⟨τ, hτ⟩ := exists_truncated_section z b hz hzb N
  have hτaug : ∀ x, τ x - algebraMap k _ (ε x) ∈ truncVarIdeal σ k N := by
    intro x
    obtain ⟨p, hp⟩ := exists_sub_aeval_mem_pow z b hz hzb x N
    have hεx : ε x = constantCoeff p := by
      have h1 : x - aeval z p ∈ RingHom.ker ε := Ideal.pow_le_self hN hp
      rw [RingHom.mem_ker, map_sub, augmentation_aeval z hz, sub_eq_zero] at h1
      exact h1
    rw [hτ x p hp, hεx, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, ← map_sub]
    exact Ideal.mem_map_of_mem _ (sub_C_constantCoeff_mem_idealOfVars p)
  have haug : ∀ (P : σ → Prop) [DecidablePred P] (x : A),
      truncKeep P N (τ x) - algebraMap k _ (ε x) ∈ truncVarIdeal σ k N := by
    intro P _ x
    have := truncKeep_mem P (hτaug x)
    rwa [map_sub, AlgHom.commutes] at this
  let τm := (truncKeep (k := k) (fun s => w s < 0) N).comp τ
  let τp := (truncKeep (k := k) (fun s => 0 < w s) N).comp τ
  have hgen : ∀ {d : ℤ} {x : A}, x ∈ 𝒜 d → ε x = 0 → ∃ p : MvPolynomial σ k,
      IsWeightedHomogeneous w p d ∧ constantCoeff p = 0 ∧ τ x = Ideal.Quotient.mk _ p := by
    intro d x hx hεx
    obtain ⟨p, hp, hc, hτx⟩ :=
      exists_isWeightedHomogeneous_of_section 𝒜 z b hε hzw hz hzb hN τ hτ hx
    exact ⟨p, hp, hc.trans hεx, hτx⟩
  have hplus : ∀ x ∈ plusIdeal 𝒜 ε, τp x = 0 := by
    have key : ∀ {d : ℤ} {x : A}, d ≤ 0 → x ∈ 𝒜 d → ε x = 0 → τp x = 0 := by
      intro d x hd hx hεx
      obtain ⟨p, hp, hc, hτx⟩ := hgen hx hεx
      simp only [τp, AlgHom.comp_apply, hτx, truncKeep_mk, keepVars_pos_eq_zero hp hd hc,
        map_zero]
    have hle : plusIdeal 𝒜 ε ≤ RingHom.ker τp := by
      rw [plusIdeal, Ideal.span_le]
      rintro x (⟨d, hd, hx⟩ | ⟨hx, hεx⟩)
      · exact SetLike.mem_coe.2 (RingHom.mem_ker.2 (key hd.le hx (hε d hd.ne _ hx)))
      · exact SetLike.mem_coe.2 (RingHom.mem_ker.2 (key le_rfl hx hεx))
    exact fun x hx => RingHom.mem_ker.1 (hle hx)
  have hminus : ∀ x ∈ minusIdeal 𝒜 ε, τm x = 0 := by
    have key : ∀ {d : ℤ} {x : A}, 0 ≤ d → x ∈ 𝒜 d → ε x = 0 → τm x = 0 := by
      intro d x hd hx hεx
      obtain ⟨p, hp, hc, hτx⟩ := hgen hx hεx
      simp only [τm, AlgHom.comp_apply, hτx, truncKeep_mk, keepVars_neg_eq_zero hp hd hc,
        map_zero]
    have hle : minusIdeal 𝒜 ε ≤ RingHom.ker τm := by
      rw [minusIdeal, Ideal.span_le]
      rintro x (⟨d, hd, hx⟩ | ⟨hx, hεx⟩)
      · exact SetLike.mem_coe.2 (RingHom.mem_ker.2 (key hd.le hx (hε d hd.ne' _ hx)))
      · exact SetLike.mem_coe.2 (RingHom.mem_ker.2 (key le_rfl hx hεx))
    exact fun x hx => RingHom.mem_ker.1 (hle hx)
  let fm := Ideal.Quotient.liftₐ (minusIdeal 𝒜 ε) τm hminus
  let fp := Ideal.Quotient.liftₐ (plusIdeal 𝒜 ε) τp hplus
  let Ψ := (Algebra.TensorProduct.productMap fm fp).comp (bigCellMap 𝒜 ε Δ)
  have hΨ : ∀ x, Ψ x = Algebra.TensorProduct.productMap τm τp (Δ x) := by
    intro x
    change Algebra.TensorProduct.productMap fm fp
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (minusIdeal 𝒜 ε))
        (Ideal.Quotient.mkₐ k (plusIdeal 𝒜 ε)) (Δ x)) = _
    generalize Δ x = t
    induction t using TensorProduct.inductionOn with
    | tmul y y' => rfl
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  have hkey : ∀ x, Ψ x - τm x - τp x + algebraMap k _ (ε x) ∈ truncVarIdeal σ k N ^ 2 := by
    intro x
    have := productMap_sub_mem_sq ε (truncVarIdeal σ k N) τm τp (haug _) (haug _) (Δ x)
    rwa [hr x, hl x, ← hΨ x] at this
  refine mem_pow_of_map_eq_zero z b hz hzb Ψ (fun s => ?_) (fun x hx => ?_) ?_
  · have hτz : τ (z s) = Ideal.Quotient.mk _ (X s) :=
      hτ _ _ (by rw [aeval_X, sub_self]; exact Ideal.zero_mem _)
    have hsum : τm (z s) + τp (z s) = Ideal.Quotient.mk _ (X s) := by
      simp only [τm, τp, AlgHom.comp_apply, hτz, truncKeep_mk, keepVars_X]
      rw [← map_add]
      congr 1
      rcases lt_or_gt_of_ne (hw s) with h | h
      · simp [h, not_lt.2 h.le]
      · simp [h, not_lt.2 h.le]
    have := hkey (z s)
    rwa [hz s, map_zero, add_zero, sub_sub, hsum] at this
  · have hεx : ε x = 0 := hx
    have h1 := hkey x
    have h2 := haug (fun s => w s < 0) x
    have h3 := haug (fun s => 0 < w s) x
    rw [hεx, map_zero, add_zero] at h1
    rw [hεx, map_zero, sub_zero] at h2 h3
    have : Ψ x = (Ψ x - τm x - τp x) + τm x + τp x := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero h1) h2) h3
  · change Algebra.TensorProduct.productMap fm fp (bigCellMap 𝒜 ε Δ a) = 0
    rw [ha, map_zero]

end Main

/-- **Graded big-cell injectivity.** -/
theorem gradedBigCellInjectivity : GradedBigCellInjectivityStatement.{u} := by
  intro k _ A _ _ _ _ _ 𝒜 _ ε Δ hε hl hr hI0
  obtain ⟨σ, b, z, w, hw, hzw, hzb⟩ := exists_homogeneous_cotangent_basis 𝒜 ε hε hI0
  have hl' : ∀ x, Algebra.TensorProduct.lid k A
      (Algebra.TensorProduct.map ε (AlgHom.id k A) (Δ x)) = x := fun x => AlgHom.congr_fun hl x
  have hr' : ∀ x, Algebra.TensorProduct.rid k k A
      (Algebra.TensorProduct.map (AlgHom.id k A) ε (Δ x)) = x := fun x => AlgHom.congr_fun hr x
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ ⨅ N : ℕ, RingHom.ker ε ^ N := by
    refine (Submodule.mem_iInf _).2 fun N => ?_
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact mem_pow_of_bigCellMap_eq_zero ε 𝒜 Δ hε hl' hr' b z w hw hzw hzb hN.ne' ha
  rwa [Ideal.iInf_pow_eq_bot_of_isDomain (RingHom.ker ε) (RingHom.ker_ne_top ε),
    Ideal.mem_bot] at hmem

end Langlands.GroupScheme.TorusUnipotence
