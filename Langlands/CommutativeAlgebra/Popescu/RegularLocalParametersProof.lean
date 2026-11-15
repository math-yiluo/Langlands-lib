import Langlands.CommutativeAlgebra.Popescu.RegularLocalParametersStatement
import Langlands.CommutativeAlgebra.RegularLocalDomainProof

/-! # Proof: minimal generators of the maximal ideal of a regular local ring are regular -/

universe u

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

namespace Langlands.CommutativeAlgebra.Popescu

namespace RegularLocalParameters

/-- An ideal spanned by the values of a family indexed by `Fin n` needs at most `n`
generators. -/
theorem spanFinrank_span_range_le {S : Type*} [CommRing S] {n : ℕ} (y : Fin n → S) :
    (Ideal.span (Set.range y)).spanFinrank ≤ n := by
  calc (Ideal.span (Set.range y)).spanFinrank ≤ (Set.range y).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range y)
    _ ≤ n := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp)

/-- If the first member of a family indexed by `Fin (n + 1)` vanishes, the family spans the
same ideal as its remaining members. -/
theorem span_range_eq_span_range_succ_of_eq_zero {S : Type*} [CommRing S] {n : ℕ}
    (z : Fin (n + 1) → S) (h0 : z 0 = 0) :
    Ideal.span (Set.range z) = Ideal.span (Set.range fun i : Fin n => z i.succ) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => rw [h0]; exact Ideal.zero_mem _
    | succ j => exact Ideal.subset_span ⟨j, rfl⟩
  · apply Ideal.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

/-- An element of `WithBot ℕ∞` that is not `⊥` and is bounded by a natural number is a
natural number. -/
theorem exists_nat_eq_of_ne_bot_of_le {a : WithBot ℕ∞} {k : ℕ} (h0 : a ≠ ⊥)
    (hk : a ≤ (k : WithBot ℕ∞)) : ∃ m : ℕ, a = (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd hk (not_le.mpr (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
    | coe m => exact ⟨m, rfl⟩

/-- Main induction: in a regular local ring whose maximal ideal needs `n` generators, a family
of `n` elements spanning the maximal ideal is a regular sequence. -/
theorem isRegular_ofFn_of_spanFinrank_eq :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R] (x : Fin n → R),
      (maximalIdeal R).spanFinrank = n → Ideal.span (Set.range x) = maximalIdeal R →
        IsRegular R (List.ofFn x) := by
  intro n
  induction n with
  | zero =>
    intro R _ _ x _ _
    rw [List.ofFn_zero]
    exact IsRegular.nil R R
  | succ n ih =>
    intro R _ _ x hn hx
    have : IsDomain R := Langlands.CommutativeAlgebra.regularLocalDomain R inferInstance
    -- The first parameter `x 0` is a nonzero element of the maximal ideal.
    have hrm : x 0 ∈ maximalIdeal R := hx ▸ Ideal.subset_span ⟨0, rfl⟩
    have hr0 : x 0 ≠ 0 := by
      intro h0
      have hle : (maximalIdeal R).spanFinrank ≤ n := by
        rw [← hx, span_range_eq_span_range_succ_of_eq_zero x h0]
        exact spanFinrank_span_range_le _
      omega
    have hreg : IsSMulRegular R (x 0) := IsSMulRegular.of_ne_zero hr0
    -- The quotient `R ⧸ (x 0)` is a Noetherian local ring.
    have hne : Ideal.span {x 0} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal (x 0)).mp hrm
    have : Nontrivial (R ⧸ Ideal.span {x 0}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ Ideal.span {x 0}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    let y' : Fin n → R ⧸ Ideal.span {x 0} := fun i => Ideal.Quotient.mk _ (x i.succ)
    have hy' : Ideal.span (Set.range y') = maximalIdeal (R ⧸ Ideal.span {x 0}) := by
      rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x 0}))
        Ideal.Quotient.mk_surjective, ← hx, Ideal.map_span, ← Set.range_comp]
      exact (span_range_eq_span_range_succ_of_eq_zero (Ideal.Quotient.mk (Ideal.span {x 0}) ∘ x)
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (x 0)))).symm
    have hs' : (maximalIdeal (R ⧸ Ideal.span {x 0})).spanFinrank ≤ n :=
      hy' ▸ spanFinrank_span_range_le y'
    -- Dimension count: `dim R ⧸ (x 0) = n`.
    have hdim : ringKrullDim (R ⧸ Ideal.span {x 0}) + 1 = ringKrullDim R :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hrm
    have hdimR : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
    have hle : ringKrullDim (R ⧸ Ideal.span {x 0}) ≤
        ((maximalIdeal (R ⧸ Ideal.span {x 0})).spanFinrank : WithBot ℕ∞) :=
      ringKrullDim_le_spanFinrank_maximalIdeal _
    obtain ⟨m, hm⟩ := exists_nat_eq_of_ne_bot_of_le ringKrullDim_ne_bot hle
    have hmn : m = n := by
      rw [hm, hdimR] at hdim
      have h : ((m + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← hdim]; push_cast; rfl
      exact Nat.succ_injective (Nat.cast_injective h)
    have hle' : m ≤ (maximalIdeal (R ⧸ Ideal.span {x 0})).spanFinrank := by
      rw [hm] at hle
      exact_mod_cast hle
    have hs'eq : (maximalIdeal (R ⧸ Ideal.span {x 0})).spanFinrank = n := by omega
    have : IsRegularLocalRing (R ⧸ Ideal.span {x 0}) :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (by rw [hs'eq, hm]; exact_mod_cast hmn.ge)
    -- Induction hypothesis for `R ⧸ (x 0)`.
    have ih' : IsRegular (R ⧸ Ideal.span {x 0}) (List.ofFn y') :=
      ih (R ⧸ Ideal.span {x 0}) y' hs'eq hy'
    -- Transfer to the `R`-module `QuotSMulTop (x 0) R = R ⧸ (x 0) • R`.
    have hsm : (x 0 • (⊤ : Submodule R R)) = (Ideal.span {x 0} : Submodule R R) := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    let e : QuotSMulTop (x 0) R ≃ₗ[R] R ⧸ Ideal.span {x 0} := Submodule.quotEquivOfEq _ _ hsm
    have htr : IsRegular (QuotSMulTop (x 0) R) (List.ofFn fun i : Fin n => x i.succ) := by
      refine (AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_).mpr ih'
      have hl : List.ofFn y' =
          (List.ofFn fun i : Fin n => x i.succ).map (Ideal.Quotient.mk (Ideal.span {x 0})) := by
        rw [List.map_ofFn]; rfl
      rw [hl, List.forall₂_map_right_iff, List.forall₂_same]
      intro a _ z
      change e (a • z) = Ideal.Quotient.mk _ a • e z
      rw [map_smul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rw [List.ofFn_succ]
    exact IsRegular.cons hreg htr

end RegularLocalParameters

open RegularLocalParameters in
/-- Stacks Project, Lemma 10.106.3 (Tag 00NQ), first assertion: a minimal generating family of
the maximal ideal of a regular local ring is a regular sequence. -/
theorem regularLocalParameters : RegularLocalParametersStatement.{u} := by
  intro R _ _ x hx
  exact isRegular_ofFn_of_spanFinrank_eq _ R x rfl hx

end Langlands.CommutativeAlgebra.Popescu
