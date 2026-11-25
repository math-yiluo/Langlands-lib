import Langlands.MathlibBase
import Langlands.CommutativeAlgebra.Popescu.ArtinianFlatClaim

/-! # The coefficient claim for an Artinian local algebra

The claim in the proof of Stacks, Smoothing Ring Maps, Lemma 16.11.1 (07FG), proved by induction
over the quotients `L ⧸ 𝔪^(j+1)`. -/

namespace Langlands.CommutativeAlgebra.Popescu.ArtinianFlat

open IsLocalRing MvPolynomial

theorem mul_mem_pow {R : Type*} [CommRing R] {I : Ideal R} {a b : R} {m n m' : ℕ}
    (ha : a ∈ I ^ m) (hb : b ∈ I ^ n) (h : m' ≤ m + n) : a * b ∈ I ^ m' :=
  Ideal.pow_le_pow_right h (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb)

section Induction

variable {k L : Type*} [Field k] [CommRing L] [Algebra k L] [IsLocalRing L]

/-- The residue map of `L ⧸ 𝔪^(j+1)`. -/
noncomputable def resQ (j : ℕ) : L ⧸ maximalIdeal L ^ (j + 1) →+* ResidueField L :=
  Ideal.Quotient.lift _ (residue L) fun x hx ↦
    (residue_eq_zero_iff x).mpr (Ideal.pow_le_self (Nat.succ_ne_zero j) hx)

theorem resQ_mk (j : ℕ) (x : L) : resQ j (Ideal.Quotient.mk _ x) = residue L x := rfl

theorem ker_resQ_le (j : ℕ) :
    RingHom.ker (resQ (L := L) j) ≤ (maximalIdeal L).map (Ideal.Quotient.mk _) := by
  intro y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, resQ_mk, residue_eq_zero_iff] at hy
  exact Ideal.mem_map_of_mem _ hy

/-- The base case of the claim: `L ⧸ 𝔪` is the residue field. -/
theorem coeffClaim_zero {d : ℕ} (t : Fin d → L) :
    CoeffClaim k (ResidueField L) (L ⧸ maximalIdeal L ^ (0 + 1)) (resQ 0)
      (fun i ↦ Ideal.Quotient.mk _ (t i)) := by
  let σ : ResidueField L →+* L ⧸ maximalIdeal L ^ (0 + 1) :=
    Ideal.Quotient.factor (S := maximalIdeal L) (T := maximalIdeal L ^ (0 + 1))
      (by rw [zero_add, pow_one])
  refine ⟨σ, fun x ↦ ?_, ⊥, IntermediateField.fg_bot, fun a ↦
    ⟨C ⟨algebraMap k _ a, IntermediateField.algebraMap_mem _ a⟩, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := residue_surjective x
    rfl
  · rw [eval₂_C]
    rfl

/-- The inductive step of the claim, from `L ⧸ 𝔪^(j+1)` to `L ⧸ 𝔪^(j+2)`. -/
theorem coeffClaim_succ (p : ℕ) [Fact p.Prime] [CharP k p]
    (hV : (LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ k (ResidueField L))).FG)
    {d : ℕ} (t : Fin d → L) (ht : Ideal.span (Set.range t) = maximalIdeal L) (j : ℕ)
    (h : CoeffClaim k (ResidueField L) (L ⧸ maximalIdeal L ^ (j + 1)) (resQ j)
      (fun i ↦ Ideal.Quotient.mk _ (t i))) :
    CoeffClaim k (ResidueField L) (L ⧸ maximalIdeal L ^ (j + 1 + 1)) (resQ (j + 1))
      (fun i ↦ Ideal.Quotient.mk _ (t i)) := by
  have hle : maximalIdeal L ^ (j + 1 + 1) ≤ maximalIdeal L ^ (j + 1) :=
    Ideal.pow_le_pow_right (by omega)
  refine coeffClaim_of_surjective p hV (Ideal.Quotient.factorₐ k hle)
    (Ideal.Quotient.factor_surjective hle) (resQ (j + 1)) (resQ j) ?_ (fun a ↦ rfl)
    (fun i ↦ Ideal.Quotient.mk _ (t i)) ?_ (n := j + 1 + 1) ?_ ?_ ?_ ?_ h
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  · intro i
    rw [resQ_mk, residue_eq_zero_iff, ← ht]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [eq_bot_iff]
    refine (Ideal.pow_right_mono (ker_resQ_le _) _).trans ?_
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
  · refine (ker_resQ_le _).trans ?_
    rw [← ht, Ideal.map_span, ← Set.range_comp]
    rfl
  · intro x y hx hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk _ x = 0 at hx
    change Ideal.Quotient.mk _ y = 0 at hy
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact mul_mem_pow hx hy (by omega)
  · intro x y hx hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk _ y = 0 at hy
    rw [resQ_mk, residue_eq_zero_iff] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact mul_mem_pow (m := 1) (by rwa [pow_one]) hy (by omega)

/-- The claim in the proof of Stacks 07FG: if `𝔪 = (t₁, …, t_d)` and `H₁(L_{κ/k})` is finite,
there are a section `σ` of the residue map and a finitely generated subextension `F` of `κ/k`
with `k ⊂ σ(F)[t₁, …, t_d]`. -/
theorem coeffClaim_residue (p : ℕ) [Fact p.Prime] [CharP k p] [IsArtinianRing L]
    (hV : (LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ k (ResidueField L))).FG)
    {d : ℕ} (t : Fin d → L) (ht : Ideal.span (Set.range t) = maximalIdeal L) :
    CoeffClaim k (ResidueField L) L (residue L) t := by
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal L) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal L).mp inferInstance
  have hall : ∀ j, CoeffClaim k (ResidueField L) (L ⧸ maximalIdeal L ^ (j + 1)) (resQ j)
      (fun i ↦ Ideal.Quotient.mk _ (t i)) := by
    intro j
    induction j with
    | zero => exact coeffClaim_zero t
    | succ j ih => exact coeffClaim_succ p hV t ht j ih
  have hn' : maximalIdeal L ^ (n + 1) = ⊥ := by
    rw [pow_succ, hn, Ideal.zero_eq_bot, Ideal.bot_mul]
  refine coeffClaim_of_surjective p hV (Ideal.Quotient.mkₐ k (maximalIdeal L ^ (n + 1)))
    (Ideal.Quotient.mkₐ_surjective k _) (residue L) (resQ n) (fun x ↦ rfl) (fun a ↦ rfl) t
    (fun i ↦ ?_) (n := n + 1) ?_ ?_ ?_ ?_ (hall n)
  · rw [residue_eq_zero_iff, ← ht]
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [ker_residue, hn']
  · rw [ker_residue, ht]
  · intro x y hx _
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hn', Ideal.mem_bot] at hx
    rw [hx, zero_mul]
  · intro x y _ hy
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hn', Ideal.mem_bot] at hy
    rw [hy, mul_zero]

end Induction

end Langlands.CommutativeAlgebra.Popescu.ArtinianFlat
