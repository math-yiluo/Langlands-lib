import Langlands.Representation.Archimedean.LowerVermaCentral
import Langlands.Representation.Archimedean.BGChaseReps

/-!
# Simple lower Verma modules with constant `Re(λ_p + p)`

If the real parts of `λ_p + p` do not depend on `p`, then the lower Verma module `M⁻(λ)` of
`𝔤𝔩_n(ℂ)` is simple and `λ` is `Z`-extremal. Both follow from the eigenvalue of the Casimir
element `C_2`: its real part strictly increases along nonzero real vectors of coordinate sum zero.
See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaSimple

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping MvPolynomial VermaGL VermaPBW VermaCentral BGChase

variable {n : ℕ}

/-! ## The Casimir eigenvalue -/

/-- The eigenvalue `Σ_a ((ν_a + a) ν_a - Σ_{c < a} ν_c)` of the Casimir element `C_2` on
`gen ν`. -/
def casC (ν : Fin n → ℂ) : ℂ := ∑ a, ((ν a + ((a : ℕ) : ℂ)) * ν a - ∑ c ∈ Finset.Iio a, ν c)

/-- Gelfand's element `C_2 = Σ_{p,q} E_pq E_qp`, as an element of the center. -/
def cas2 (n : ℕ) : center n := ⟨gel n 2, gel_mem_center n 2⟩

theorem eval_gamC_cas2 (ν : Fin n → ℂ) : eval ν (gamC n (cas2 n)) = casC ν := by
  have h1 : ∀ a, eval ν (ComplexJacquetFinite.gelPoly n 1 a) = ν a := by
    intro a
    rw [ComplexJacquetFinite.gelPoly_succ]
    simp [ComplexJacquetFinite.gelPoly_zero, Fin.card_Iio]
  show eval ν (gam n (gel n 2)) = casC ν
  rw [gam_gel, map_sum, casC]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ComplexJacquetFinite.gelPoly_succ]
  simp [h1]

theorem casC_add_sub (lam β : Fin n → ℂ) :
    casC (lam + β) - casC lam =
      ∑ a, (β a * (2 * lam a + ((a : ℕ) : ℂ)) + β a ^ 2) - ∑ a, ∑ c ∈ Finset.Iio a, β c := by
  rw [casC, casC, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem sum_Iio_eq (b : Fin n → ℝ) :
    ∑ a, ∑ c ∈ Finset.Iio a, b c = ∑ c : Fin n, ((n : ℝ) - 1 - ((c : ℕ) : ℝ)) * b c := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun c => Finset.Ioi c) (by intro x y; simp)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Fin.card_Ioi, nsmul_eq_mul]
  congr 1
  have hc : (c : ℕ) < n := c.2
  have h1 : 1 ≤ n := by omega
  have h2 : (c : ℕ) ≤ n - 1 := by omega
  rw [Nat.cast_sub h2, Nat.cast_sub h1, Nat.cast_one]

/-- If `Re(λ_p) + p` is constant and `b` is real with coordinate sum zero, then
`Re C(λ + b) = Re C(λ) + Σ b_r²`. -/
theorem re_casC_add {lam : Fin n → ℂ}
    (hre : ∀ p q : Fin n, (lam p).re + ((p : ℕ) : ℝ) = (lam q).re + ((q : ℕ) : ℝ))
    (b : Fin n → ℝ) (hb : ∑ r, b r = 0) :
    (casC (lam + fun r => (b r : ℂ))).re = (casC lam).re + ∑ r, b r ^ 2 := by
  have h := congrArg Complex.re (casC_add_sub lam fun r => (b r : ℂ))
  have hlin : ∑ a, b a * ((lam a).re + ((a : ℕ) : ℝ)) = 0 := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨q⟩⟩
    · simp [Finset.univ_eq_empty]
    · rw [Finset.sum_congr rfl fun a _ => by rw [hre a q], ← Finset.sum_mul, hb, zero_mul]
  have hA : ∑ a, b a * (2 * (lam a).re + ((a : ℕ) : ℝ)) =
      2 * ∑ a, b a * ((lam a).re + ((a : ℕ) : ℝ)) - ∑ a : Fin n, ((a : ℕ) : ℝ) * b a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hB : ∑ c : Fin n, ((n : ℝ) - 1 - ((c : ℕ) : ℝ)) * b c =
      ((n : ℝ) - 1) * ∑ c, b c - ∑ c : Fin n, ((c : ℕ) : ℝ) * b c := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hR : (∑ a, ((b a : ℂ) * (2 * lam a + ((a : ℕ) : ℂ)) + (b a : ℂ) ^ 2) -
      ∑ a, ∑ c ∈ Finset.Iio a, (b c : ℂ)).re =
      ∑ a, b a * (2 * (lam a).re + ((a : ℕ) : ℝ)) + ∑ r, b r ^ 2 -
        ∑ a, ∑ c ∈ Finset.Iio a, b c := by
    rw [Complex.sub_re, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp [pow_two, Complex.mul_re]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Complex.re_sum]
      simp
  rw [Complex.sub_re, hR, sum_Iio_eq, hA, hB, hlin, hb] at h
  linarith

/-! ## The positive root cone -/

theorem cone_sum {v : Fin n → ℂ} (hv : v ∈ posRootCone n) : ∑ r, v r = 0 := by
  unfold VermaGL.posRootCone at hv
  induction hv using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨p, q, -, rfl⟩ := hx
    simp [Finset.sum_sub_distrib]
  | zero => simp
  | add x y _ _ hx hy => simp [Finset.sum_add_distrib, hx, hy]

theorem cone_im {v : Fin n → ℂ} (hv : v ∈ posRootCone n) (r : Fin n) : (v r).im = 0 := by
  unfold VermaGL.posRootCone at hv
  induction hv using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨p, q, -, rfl⟩ := hx
    simp only [Pi.sub_apply, Complex.sub_im, Pi.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]

/-! ## Weights -/

/-- The operators `H_p = E_pp - λ_p` on `M⁻(λ)`. -/
def Hd (lam : Fin n → ℂ) (p : Fin n) : Module.End ℂ (LowerVerma n lam) :=
  action n lam (Matrix.single p p 1) - lam p • LinearMap.id

theorem Hd_apply (lam : Fin n → ℂ) (p : Fin n) (x : LowerVerma n lam) :
    Hd lam p x = unitU n p p • x - lam p • x := rfl

/-- An integral vector `m`, viewed in `ℂⁿ`. -/
def wc (m : Fin n → ℤ) : Fin n → ℂ := fun p => (m p : ℂ)

theorem wc_add (x y : Fin n → ℤ) : wc (x + y) = wc x + wc y := by
  funext p
  simp [wc]

theorem wc_sub (x y : Fin n → ℤ) : wc (x - y) = wc x - wc y := by
  funext p
  simp [wc]

theorem wc_single (a : Fin n) : wc (Pi.single a 1) = Pi.single a 1 := by
  funext p
  simp only [wc, Pi.single_apply]
  split_ifs <;> simp

theorem cast_single (a p : Fin n) :
    (((Pi.single a (1 : ℤ) : Fin n → ℤ) p : ℤ) : ℂ) = (Pi.single p (1 : ℂ) : Fin n → ℂ) a := by
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem unitU_comm_diag (a b p : Fin n) :
    unitU n p p * unitU n a b =
      unitU n a b * unitU n p p +
        ((Pi.single p (1 : ℂ) : Fin n → ℂ) a - (Pi.single p (1 : ℂ) : Fin n → ℂ) b) • unitU n a b := by
  have h := ι_diagonal_mul n (Pi.single p 1) (a, b)
  rw [Matrix.diagonal_single] at h
  exact h

/-- `E_ab` shifts weights by `ε_a - ε_b`. -/
theorem isWt_unitU {lam : Fin n → ℂ} {m : Fin n → ℤ} {u : LowerVerma n lam}
    (hu : IsWt (Hd lam) m u) (a b : Fin n) :
    IsWt (Hd lam) (m + Pi.single a 1 - Pi.single b 1) (unitU n a b • u) := by
  intro p
  have hu' : unitU n p p • u = (lam p + (m p : ℂ)) • u := by
    have h := hu p
    rw [Hd_apply, sub_eq_iff_eq_add] at h
    rw [h, add_smul, add_comm]
  rw [Hd_apply, ← mul_smul, unitU_comm_diag, add_smul, mul_smul, hu', smul_comm, smul_assoc,
    ← add_smul, ← sub_smul]
  congr 1
  rw [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add, cast_single, cast_single]
  ring

theorem isWt_W_smul_gen (lam : Fin n → ℂ) (l : List (Idx n)) (hl : ∀ c ∈ l, c.1 < c.2) :
    ∃ m, wc m ∈ posRootCone n ∧ IsWt (Hd lam) m (W n l • gen n lam) := by
  induction l with
  | nil =>
    refine ⟨0, ?_, fun p => ?_⟩
    · have h0 : wc (0 : Fin n → ℤ) = 0 := by funext p; simp [wc]
      rw [h0]
      exact zero_mem _
    · rw [W_nil, one_smul, Hd_apply, unitU_smul_gen, sub_self]
      simp
  | cons c l ih =>
    obtain ⟨m, hm, hw⟩ := ih fun d hd => hl d (List.mem_cons_of_mem c hd)
    refine ⟨m + Pi.single c.1 1 - Pi.single c.2 1, ?_, ?_⟩
    · rw [wc_sub, wc_add, wc_single, wc_single, add_sub_assoc]
      exact add_mem hm (AddSubmonoid.subset_closure ⟨c.1, c.2, hl c List.mem_cons_self, rfl⟩)
    · rw [W_cons, mul_smul]
      exact isWt_unitU hw c.1 c.2

/-- The span of the weight spaces of weight in `Q₊`. -/
def coneSp (lam : Fin n → ℂ) : Submodule ℂ (LowerVerma n lam) :=
  ⨆ (m : Fin n → ℤ) (_ : wc m ∈ posRootCone n), wtSpace (Hd lam) m

theorem coneSp_eq_top (lam : Fin n → ℂ) : coneSp lam = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hu : u ∈ Submodule.span ℂ (Set.range (basisU n)) := by
    rw [(basisU n).span_eq]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, rfl⟩ := hu
    rw [mk_eq_smul_gen, basisU_smul_gen]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨m, hm, hw⟩ := isWt_W_smul_gen lam (Kostant.expand ((upList n).map Subtype.val) α)
      fun c hc => by
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp (mem_expand hc)
        exact c'.2
    exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem hm (mem_wtSpace.2 hw))
  | zero => rw [Submodule.Quotient.mk_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ r hx

/-- Every nonzero weight vector of `M⁻(λ)` has weight in `λ + Q₊`. -/
theorem cone_of_isWt {lam : Fin n → ℂ} {m : Fin n → ℤ} {u : LowerVerma n lam}
    (hu : IsWt (Hd lam) m u) (hne : u ≠ 0) : wc m ∈ posRootCone n := by
  classical
  by_contra hP
  have hmem : u ∈ coneSp lam := by rw [coneSp_eq_top]; trivial
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  have hf0 : f m = 0 := by
    have h := hf m
    rwa [iSup_neg hP, Submodule.mem_bot] at h
  have hfw : ∀ k, IsWt (Hd lam) k (f k) := by
    intro k
    by_cases hk : wc k ∈ posRootCone n
    · have h := hf k
      rw [iSup_pos hk] at h
      exact mem_wtSpace.1 h
    · have h := hf k
      rw [iSup_neg hk, Submodule.mem_bot] at h
      intro p
      rw [h, map_zero, smul_zero]
  set w : (Fin n → ℤ) → LowerVerma n lam := fun k => f k - if k = m then u else 0 with hwdef
  have hw : ∀ k ∈ insert m f.support, IsWt (Hd lam) k (w k) := by
    intro k _ p
    by_cases hk : k = m
    · subst hk
      simp only [hwdef, ite_true, hf0, zero_sub, map_neg, hu p, smul_neg]
    · simp only [hwdef, hk, ite_false, sub_zero]
      exact hfw k p
  have hs : ∑ k ∈ insert m f.support, w k = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_insert_self _ _),
      ← Finset.sum_subset (Finset.subset_insert m f.support), sub_eq_zero]
    · exact hsum
    · intro k _ hk
      exact Finsupp.notMem_support_iff.1 hk
  have h := mem_of_sum_mem (Hd lam) ⊥ (fun p x hx => by
      rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]) (insert m f.support) w hw (by rw [hs]; exact zero_mem _) m
    (Finset.mem_insert_self _ _)
  rw [Submodule.mem_bot] at h
  simp only [hwdef, ite_true, hf0, zero_sub, neg_eq_zero] at h
  exact hne h

/-- The integral height `-Σ_r r m_r`. -/
def hz (m : Fin n → ℤ) : ℤ := ∑ r : Fin n, -((r : ℕ) : ℤ) * m r

theorem hgt_wc (m : Fin n → ℤ) : hgt n (wc m) = (hz m : ℝ) := by
  simp [hgt, hz, wc]

theorem hz_nonneg {m : Fin n → ℤ} (hm : wc m ∈ posRootCone n) : 0 ≤ hz m := by
  have h0 : 0 ≤ hgt n (wc m) := by
    rcases cone_hgt n hm with h | h
    · rw [h]
      simp [hgt]
    · linarith
  rw [hgt_wc] at h0
  exact_mod_cast h0

theorem hz_step (m : Fin n → ℤ) (a b : Fin n) :
    hz (m + Pi.single a 1 - Pi.single b 1) = hz m - ((a : ℕ) : ℤ) + ((b : ℕ) : ℤ) := by
  simp only [hz, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

/-! ## The Casimir element on primitive vectors -/

/-- The center acts on `M⁻(λ)` through the central character of `gen λ`. -/
theorem center_smul {lam : Fin n → ℂ} (z : center n) (x : LowerVerma n lam) :
    (z : glU n) • x = eval lam (gamC n z) • x := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_smul_gen, smul_smul, ← Subalgebra.mem_center_iff.1 z.2 u, mul_smul,
    eval_gamC_smul_gen, smul_comm]

/-- A vector of weight `w` killed by the lower triangular matrix units has the central character
of `M⁻(w)`. -/
theorem center_smul_of_primitive {lam : Fin n → ℂ} (z : center n) (w : Fin n → ℂ)
    (u : LowerVerma n lam) (hlow : ∀ a b : Fin n, b < a → unitU n a b • u = 0)
    (hwt : ∀ p, unitU n p p • u = w p • u) :
    (z : glU n) • u = eval w (gamC n z) • u := by
  have hle : lowerVermaIdeal n w ≤
      LinearMap.ker (LinearMap.toSpanSingleton (glU n) (LowerVerma n lam) u) := by
    rw [lowerVermaIdeal, Submodule.span_le]
    rintro x (⟨a, b, hab, rfl⟩ | ⟨p, rfl⟩)
    · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hlow a b hab
    · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, hwt p,
        algebraMap_smul, sub_self]
  have hmem : (z : glU n) - algebraMap ℂ (glU n) (eval w (gamC n z)) ∈ lowerVermaIdeal n w := by
    have h := eval_gamC_smul_gen n z w
    simp only [VermaGL.gen] at h
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      Submodule.Quotient.eq] at h
    rwa [Algebra.algebraMap_eq_smul_one]
  have h0 := hle hmem
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, algebraMap_smul,
    sub_eq_zero] at h0
  exact h0

theorem casC_ne_of_wt {lam : Fin n → ℂ}
    (hre : ∀ p q : Fin n, (lam p).re + ((p : ℕ) : ℝ) = (lam q).re + ((q : ℕ) : ℝ))
    {m : Fin n → ℤ} (hm : wc m ∈ posRootCone n) (hne : m ≠ 0) :
    casC (lam + wc m) ≠ casC lam := by
  intro h
  have hsumZ : ∑ r, m r = 0 := by
    have := cone_sum hm
    simp only [wc] at this
    exact_mod_cast this
  have hsum : ∑ r, (m r : ℝ) = 0 := by exact_mod_cast hsumZ
  have hwc : wc m = fun r => ((m r : ℝ) : ℂ) := by
    funext r
    simp [wc]
  have h2 := re_casC_add hre (fun r => (m r : ℝ)) hsum
  rw [← hwc, h] at h2
  have hsq : ∑ r, (m r : ℝ) ^ 2 = 0 := by linarith
  apply hne
  funext r
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg ((m r : ℝ)))).1 hsq r
    (Finset.mem_univ _)
  have h4 : (m r : ℝ) = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
  exact_mod_cast h4

/-! ## The theorems -/

/-- If `Re(λ_p) + p` does not depend on `p`, then `λ` is `Z`-extremal. -/
theorem isZExtremal_of_re {lam : Fin n → ℂ}
    (hre : ∀ p q : Fin n, (lam p).re + ((p : ℕ) : ℝ) = (lam q).re + ((q : ℕ) : ℝ)) :
    IsZExtremal n lam := by
  intro μ hμ hne
  refine ⟨gel n 2, gel_mem_center n 2, casC lam, ?_, ?_⟩
  · have h := eval_gamC_smul_gen n (cas2 n) lam
    rw [eval_gamC_cas2] at h
    exact h
  · intro h
    have h' := eval_gamC_smul_gen n (cas2 n) μ
    rw [eval_gamC_cas2] at h'
    have heq : casC μ = casC lam := smul_left_injective ℂ (gen_ne_zero n μ) (h'.symm.trans h)
    set v := lam - μ with hv
    have hb : μ = lam + fun r => ((-(v r).re : ℝ) : ℂ) := by
      funext r
      have him := cone_im hμ r
      simp only [hv, Pi.sub_apply, Complex.sub_im] at him
      apply Complex.ext
      · simp [hv]
      · simp only [Pi.add_apply, Complex.add_im, Complex.ofReal_im, add_zero]
        linarith
    have hsum : ∑ r, (-(v r).re) = 0 := by
      rw [Finset.sum_neg_distrib, ← Complex.re_sum, cone_sum hμ, Complex.zero_re, neg_zero]
    have h2 := re_casC_add hre _ hsum
    rw [← hb, heq] at h2
    have hsq : ∑ r, (-(v r).re) ^ 2 = 0 := by linarith
    apply hne
    funext r
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => sq_nonneg (-(v r).re))).1 hsq r
      (Finset.mem_univ _)
    have h4 : (v r).re = 0 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.1 h3
      linarith
    have h5 : v r = 0 := Complex.ext (by simpa using h4) (by simpa using cone_im hμ r)
    rw [hv, Pi.sub_apply, sub_eq_zero] at h5
    exact h5.symm

/-- If `Re(λ_p) + p` does not depend on `p`, every nonzero submodule of `M⁻(λ)` contains
`gen λ`. -/
theorem gen_mem_of_ne_bot {lam : Fin n → ℂ}
    (hre : ∀ p q : Fin n, (lam p).re + ((p : ℕ) : ℝ) = (lam q).re + ((q : ℕ) : ℝ))
    (N : Submodule (glU n) (LowerVerma n lam)) (hN : N ≠ ⊥) : gen n lam ∈ N := by
  classical
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  have hstab : ∀ p, ∀ y ∈ N.restrictScalars ℂ, Hd lam p y ∈ N.restrictScalars ℂ := by
    intro p y hy
    rw [Submodule.restrictScalars_mem] at hy ⊢
    rw [Hd_apply]
    exact N.sub_mem (N.smul_mem _ hy) (N.smul_of_tower_mem (lam p) hy)
  have hxint : x ∈ intSpan (Hd lam) := by
    have hle : coneSp lam ≤ intSpan (Hd lam) :=
      iSup₂_le fun m _ w hw => mem_intSpan_of_isWt (mem_wtSpace.1 hw)
    exact hle (by rw [coneSp_eq_top]; trivial)
  have hspan := mem_span_wt_of_mem (Hd lam) (N.restrictScalars ℂ) hstab hxN hxint
  obtain ⟨u, ⟨huN, m, hum⟩, hu0⟩ :
      ∃ u ∈ {w | w ∈ N.restrictScalars ℂ ∧ ∃ m, IsWt (Hd lam) m w}, u ≠ 0 := by
    by_contra h
    push Not at h
    rw [Submodule.span_eq_bot.2 h, Submodule.mem_bot] at hspan
    exact hx0 hspan
  rw [Submodule.restrictScalars_mem] at huN
  let Q : ℕ → Prop := fun k => ∃ (m : Fin n → ℤ) (u : LowerVerma n lam),
    u ∈ N ∧ u ≠ 0 ∧ IsWt (Hd lam) m u ∧ hz m = (k : ℤ)
  have hQ : ∃ k, Q k := ⟨(hz m).toNat, m, u, huN, hu0, hum,
    (Int.toNat_of_nonneg (hz_nonneg (cone_of_isWt hum hu0))).symm⟩
  obtain ⟨m₀, u₀, hu₀N, hu₀0, hu₀, hk₀⟩ := Nat.find_spec hQ
  have hlow : ∀ a b : Fin n, b < a → unitU n a b • u₀ = 0 := by
    intro a b hab
    by_contra hne
    have hw := isWt_unitU hu₀ a b
    have hnn := hz_nonneg (cone_of_isWt hw hne)
    have hstep := hz_step m₀ a b
    have hab' : (b : ℕ) < (a : ℕ) := hab
    have hlt : (hz (m₀ + Pi.single a 1 - Pi.single b 1)).toNat < Nat.find hQ := by omega
    exact Nat.find_min hQ hlt ⟨_, _, N.smul_mem _ hu₀N, hne, hw,
      (Int.toNat_of_nonneg hnn).symm⟩
  have hwt : ∀ p, unitU n p p • u₀ = (lam + wc m₀) p • u₀ := by
    intro p
    have h := hu₀ p
    rw [Hd_apply, sub_eq_iff_eq_add] at h
    rw [h, Pi.add_apply, add_smul, add_comm]
    rfl
  have h1 := center_smul_of_primitive (cas2 n) (lam + wc m₀) u₀ hlow hwt
  have h2 := center_smul (cas2 n) u₀
  rw [eval_gamC_cas2] at h1 h2
  have heq : casC (lam + wc m₀) = casC lam := smul_left_injective ℂ hu₀0 (h1.symm.trans h2)
  have hm0 : m₀ = 0 := by
    by_contra hne
    exact casC_ne_of_wt hre (cone_of_isWt hu₀ hu₀0) hne heq
  subst hm0
  obtain ⟨c, hc⟩ := (lowerVermaWeight n lam).2 u₀ fun p => by
    rw [hwt p]
    simp [wc]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hu₀0 hc
  have hgen : gen n lam = c⁻¹ • u₀ := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hgen]
  exact N.smul_of_tower_mem _ hu₀N

/-- **Simplicity.** If `Re(λ_p) + p` does not depend on `p`, a submodule of `M⁻(λ)` not
containing `gen λ` is zero. -/
theorem eq_bot_of_gen_not_mem {lam : Fin n → ℂ}
    (hre : ∀ p q : Fin n, (lam p).re + ((p : ℕ) : ℝ) = (lam q).re + ((q : ℕ) : ℝ))
    (N : Submodule (glU n) (LowerVerma n lam)) (hN : gen n lam ∉ N) : N = ⊥ := by
  by_contra h
  exact hN (gen_mem_of_ne_bot hre N h)

end Langlands.Archimedean.VermaSimple
