import Langlands.CommutativeAlgebra.Popescu.RegularSequencePowersStatement

/-! # Proof of Stacks Lemma 10.68.9 (07DV): powers of a regular sequence -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open RingTheory.Sequence
open scoped Pointwise

namespace RegularSequencePowers

variable {R : Type*} [CommRing R]

section Module

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem mk_eq_zero_iff (a : R) (m : M) :
    (Submodule.Quotient.mk m : QuotSMulTop a M) = 0 ↔ ∃ n : M, a • n = m := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- If `f` is `M`-regular and `g` is regular on `M/fM`, then `f` is regular on `M/gM`. -/
theorem isSMulRegular_quot_swap {f g : R} (hf : IsSMulRegular M f)
    (hg : IsSMulRegular (QuotSMulTop f M) g) : IsSMulRegular (QuotSMulTop g M) f := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hg ⊢
  intro z hz
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul, mk_eq_zero_iff] at hz
  obtain ⟨n, hn⟩ := hz
  have h1 : (Submodule.Quotient.mk n : QuotSMulTop f M) = 0 := by
    apply hg
    rw [← Submodule.Quotient.mk_smul, hn, mk_eq_zero_iff]
    exact ⟨m, rfl⟩
  rw [mk_eq_zero_iff] at h1
  obtain ⟨n', rfl⟩ := h1
  rw [mk_eq_zero_iff]
  refine ⟨n', hf ?_⟩
  simp only
  rw [smul_comm, hn]

/-- Regularity modulo `f` implies regularity modulo `f^(e+1)`, for `f` regular. -/
theorem isSMulRegular_quot_pow_of {f g : R} (hf : IsSMulRegular M f)
    (hg : IsSMulRegular (QuotSMulTop f M) g) (e : ℕ) :
    IsSMulRegular (QuotSMulTop (f ^ (e + 1)) M) g := by
  induction e with
  | zero => rw [zero_add, pow_one]; exact hg
  | succ e ih =>
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hg ih ⊢
    intro z hz
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← Submodule.Quotient.mk_smul, mk_eq_zero_iff] at hz
    obtain ⟨n, hn⟩ := hz
    have h1 : (Submodule.Quotient.mk m : QuotSMulTop f M) = 0 := by
      apply hg
      rw [← Submodule.Quotient.mk_smul, ← hn, mk_eq_zero_iff]
      exact ⟨f ^ (e + 1) • n, by rw [← mul_smul, ← pow_succ']⟩
    rw [mk_eq_zero_iff] at h1
    obtain ⟨m', rfl⟩ := h1
    have h2 : (Submodule.Quotient.mk m' : QuotSMulTop (f ^ (e + 1)) M) = 0 := by
      apply ih
      rw [← Submodule.Quotient.mk_smul, mk_eq_zero_iff]
      refine ⟨n, hf ?_⟩
      simp only
      rw [← mul_smul, ← pow_succ', hn, smul_comm]
    rw [mk_eq_zero_iff] at h2
    obtain ⟨p, rfl⟩ := h2
    rw [mk_eq_zero_iff]
    exact ⟨p, by rw [← mul_smul, ← pow_succ']⟩

/-- Regularity modulo `f^(e+1)` implies regularity modulo `f`, for `f` regular. -/
theorem isSMulRegular_quot_of_pow {f g : R} (hf : IsSMulRegular M f) (e : ℕ)
    (hg : IsSMulRegular (QuotSMulTop (f ^ (e + 1)) M) g) :
    IsSMulRegular (QuotSMulTop f M) g := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hg ⊢
  intro z hz
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul, mk_eq_zero_iff] at hz
  obtain ⟨n, hn⟩ := hz
  have h1 : (Submodule.Quotient.mk (f ^ e • m) : QuotSMulTop (f ^ (e + 1)) M) = 0 := by
    apply hg
    rw [← Submodule.Quotient.mk_smul, mk_eq_zero_iff]
    exact ⟨n, by rw [smul_comm, ← hn, ← mul_smul, ← pow_succ]⟩
  rw [mk_eq_zero_iff] at h1
  obtain ⟨p, hp⟩ := h1
  rw [mk_eq_zero_iff]
  refine ⟨p, (hf.pow e) ?_⟩
  simp only
  rw [← mul_smul, ← pow_succ, hp]

theorem pow_smul_top_eq_top {f : R} (h1 : (f • ⊤ : Submodule R M) = ⊤) (e : ℕ) :
    (f ^ (e + 1) • ⊤ : Submodule R M) = ⊤ := by
  induction e with
  | zero => rw [zero_add, pow_one]; exact h1
  | succ e ih => rw [pow_succ, mul_smul, h1, ih]

theorem nontrivial_quot_pow_iff (f : R) (e : ℕ) :
    Nontrivial (QuotSMulTop (f ^ (e + 1)) M) ↔ Nontrivial (QuotSMulTop f M) := by
  rw [Submodule.Quotient.nontrivial_iff, Submodule.Quotient.nontrivial_iff]
  constructor
  · intro h h1
    exact h (pow_smul_top_eq_top h1 e)
  · intro h h1
    apply h
    apply top_le_iff.mp
    calc (⊤ : Submodule R M) = f ^ (e + 1) • ⊤ := h1.symm
      _ ≤ f • ⊤ := by
        intro m hm
        rw [Submodule.mem_smul_pointwise_iff_exists] at hm ⊢
        obtain ⟨b, -, rfl⟩ := hm
        exact ⟨f ^ e • b, trivial, by rw [← mul_smul, ← pow_succ']⟩

theorem isRegular_nil_iff (N : Type*) [AddCommGroup N] [Module R N] :
    IsRegular N ([] : List R) ↔ Nontrivial N := by
  rw [isRegular_iff]
  simp only [IsWeaklyRegular.nil, true_and, Ideal.ofList_nil, Submodule.bot_smul]
  rw [← Submodule.nontrivial_iff_ne_bot]
  constructor
  · intro h
    exact (Submodule.topEquiv : (⊤ : Submodule R N) ≃ₗ[R] N).symm.toEquiv.nontrivial
  · intro h
    exact (Submodule.topEquiv : (⊤ : Submodule R N) ≃ₗ[R] N).toEquiv.nontrivial

/-- `(M/aM)/b = (M/bM)/a`. -/
noncomputable def swapEquiv (a b : R) :
    QuotSMulTop b (QuotSMulTop a M) ≃ₗ[R] QuotSMulTop a (QuotSMulTop b M) :=
  have h : ∀ x y : R, (y • ⊤ : Submodule R (QuotSMulTop x M)) =
      (y • (⊤ : Submodule R M)).map (x • (⊤ : Submodule R M)).mkQ := fun x y => by
    rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]
  let e₁ : QuotSMulTop b (QuotSMulTop a M) ≃ₗ[R] M ⧸ (a • ⊤ ⊔ b • ⊤ : Submodule R M) :=
    (Submodule.quotEquivOfEq _ _ (h a b)).trans (Submodule.quotientQuotientEquivQuotientSup _ _)
  let e₂ : QuotSMulTop a (QuotSMulTop b M) ≃ₗ[R] M ⧸ (b • ⊤ ⊔ a • ⊤ : Submodule R M) :=
    (Submodule.quotEquivOfEq _ _ (h b a)).trans (Submodule.quotientQuotientEquivQuotientSup _ _)
  e₁.trans ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans e₂.symm)

end Module

/-- Regular sequences modulo `f` and modulo `f^(e+1)` agree when `f` is regular. -/
theorem isRegular_quot_pow_iff (g : List R) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M] (f : R) (e : ℕ), IsSMulRegular M f →
      (IsRegular (QuotSMulTop (f ^ (e + 1)) M) g ↔ IsRegular (QuotSMulTop f M) g) := by
  induction g with
  | nil =>
    intro M _ _ f e _
    rw [isRegular_nil_iff, isRegular_nil_iff]
    exact nontrivial_quot_pow_iff f e
  | cons g₁ g' ih =>
    intro M _ _ f e hf
    rw [isRegular_cons_iff, isRegular_cons_iff]
    have key : IsSMulRegular (QuotSMulTop f M) g₁ →
        (IsRegular (QuotSMulTop g₁ (QuotSMulTop (f ^ (e + 1)) M)) g' ↔
          IsRegular (QuotSMulTop g₁ (QuotSMulTop f M)) g') := fun hg₁ => by
      have hf' : IsSMulRegular (QuotSMulTop g₁ M) f := isSMulRegular_quot_swap hf hg₁
      rw [(swapEquiv (f ^ (e + 1)) g₁).isRegular_congr, (swapEquiv f g₁).isRegular_congr]
      exact ih (QuotSMulTop g₁ M) f e hf'
    constructor
    · rintro ⟨h1, h2⟩
      have hg₁ := isSMulRegular_quot_of_pow hf e h1
      exact ⟨hg₁, (key hg₁).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨isSMulRegular_quot_pow_of hf h1 e, (key h1).mpr h2⟩

theorem powers_aux (r : ℕ) : ∀ (M : Type*) [AddCommGroup M] [Module R M] (f : Fin r → R)
    (e : Fin r → ℕ), (∀ i, 0 < e i) →
    (IsRegular M (List.ofFn f) ↔ IsRegular M (List.ofFn fun i => f i ^ e i)) := by
  induction r with
  | zero => intro M _ _ f e _; simp
  | succ r ih =>
    intro M _ _ f e he
    rw [List.ofFn_succ, List.ofFn_succ, isRegular_cons_iff, isRegular_cons_iff]
    obtain ⟨k, hk⟩ : ∃ k, e 0 = k + 1 := Nat.exists_eq_succ_of_ne_zero (he 0).ne'
    have hk' : f 0 ^ e 0 = f 0 ^ (k + 1) := by rw [hk]
    rw [hk']
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1.pow _, ?_⟩
      have h3 := (ih (QuotSMulTop (f 0) M) (fun i => f i.succ) (fun i => e i.succ)
        (fun i => he _)).mp h2
      exact (isRegular_quot_pow_iff _ M (f 0) k h1).mpr h3
    · rintro ⟨h1, h2⟩
      have hf0 : IsSMulRegular M (f 0) := by
        rw [pow_succ] at h1
        exact h1.of_mul
      refine ⟨hf0, (ih (QuotSMulTop (f 0) M) (fun i => f i.succ) (fun i => e i.succ)
        (fun i => he _)).mpr ((isRegular_quot_pow_iff _ M (f 0) k hf0).mp h2)⟩

end RegularSequencePowers

/-- Stacks Lemma 10.68.9 (07DV): `f₁, …, f_r` is `M`-regular iff `f₁^{e₁}, …, f_r^{e_r}` is. -/
theorem regularSequencePowers : RegularSequencePowersStatement.{u} :=
  fun _ M _ _ _ r f e he => RegularSequencePowers.powers_aux r M f e he

end Langlands.CommutativeAlgebra.Popescu
