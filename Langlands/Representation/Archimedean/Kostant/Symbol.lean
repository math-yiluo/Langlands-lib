import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.Ideal.Operations
import Langlands.Algebra.UniversalEnvelopingSymmetrization

/-!
# Symbols of elements of the universal enveloping algebra through derivations

Let `ρ` be a representation of a Lie algebra `L` on a commutative algebra `R` by derivations,
let `𝔪` be an ideal of `R`, `ε : R → S` an algebra map vanishing on `𝔪` and `l ∈ 𝔪`. For
`P ∈ U(L)` the degree-`N` symbol is `σ_N(P) = ε(ρ(P) lᴺ) / N!`. A product of `M ≤ N`
derivations applied to `fᴺ`, `f ∈ 𝔪`, is `N!/(N-M)! · f^{N-M} · ∏ D_t f` modulo `𝔪^{N-M+1}`,
so `σ_N` sends a word `x₁ ⋯ x_N` to `∏ ξ(x_t)`, where `ξ(x) = ε(ρ(x) l)`, and kills shorter
words. Hence `σ_N` vanishes on the filtration piece `U_{N-1}`, is multiplicative on
`U_a × U_b`, and turns commutators with `x ∈ L` into derivations of `S`.
-/

noncomputable section

set_option autoImplicit false

open scoped Nat

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping

/-! ## Leibniz endomorphisms and powers of an ideal -/

section Leibniz

variable {K : Type*} [CommRing K] {R : Type*} [CommRing R] [Algebra K R]

/-- A linear endomorphism satisfying the Leibniz rule (a derivation of `R`). -/
def IsLeibniz (D : Module.End K R) : Prop :=
  ∀ a b : R, D (a * b) = a * D b + D a * b

theorem IsLeibniz.map_pow_succ {D : Module.End K R} (hD : IsLeibniz D) (f : R) (k : ℕ) :
    D (f ^ (k + 1)) = (k + 1 : ℕ) • (f ^ k * D f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, hD, ih, succ_nsmul _ (k + 1), pow_succ]
    simp only [nsmul_eq_mul]
    ring

/-- A derivation maps `I^(k+1)` into `I^k`. -/
theorem IsLeibniz.map_mem_pow {D : Module.End K R} (hD : IsLeibniz D) (I : Ideal R) :
    ∀ (k : ℕ) {a : R}, a ∈ I ^ (k + 1) → D a ∈ I ^ k := by
  intro k
  induction k with
  | zero => intro a _; simp
  | succ k ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [hD]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hx (ih hy)
      · exact Ideal.mul_mem_left _ _ hy
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- A product of `M ≤ N` derivations applied to `fᴺ`, `f ∈ I`: modulo `I^(N-M+1)` it is
`N!/(N-M)! · f^(N-M) · ∏ D_t f`. -/
theorem IsLeibniz.prod_apply_pow_sub_mem (I : Ideal R) {f : R} (hf : f ∈ I) :
    ∀ (Ds : List (Module.End K R)), (∀ D ∈ Ds, IsLeibniz D) → ∀ N : ℕ, Ds.length ≤ N →
      Ds.prod (f ^ N) - N.descFactorial Ds.length •
          (f ^ (N - Ds.length) * (Ds.map fun D => D f).prod) ∈ I ^ (N - Ds.length + 1) := by
  intro Ds
  induction Ds with
  | nil => intro _ N _; simp
  | cons D Ds ih =>
    intro hDs N hN
    simp only [List.length_cons] at hN ⊢
    have hD : IsLeibniz D := hDs D List.mem_cons_self
    have hrest := ih (fun E hE => hDs E (List.mem_cons_of_mem _ hE)) N (by omega)
    obtain ⟨k, hk⟩ : ∃ k, N - Ds.length = k + 1 := ⟨N - Ds.length - 1, by omega⟩
    have hk' : N - (Ds.length + 1) = k := by omega
    rw [hk] at hrest
    rw [hk', show k + 1 = k + 1 from rfl]
    set r := Ds.prod (f ^ N) - N.descFactorial Ds.length •
      (f ^ (k + 1) * (Ds.map fun D => D f).prod) with hr
    set pr := (Ds.map fun D => D f).prod
    have hprod : Ds.prod (f ^ N) = r + N.descFactorial Ds.length • (f ^ (k + 1) * pr) := by
      rw [hr]; abel
    have hdesc : N.descFactorial (Ds.length + 1) = (k + 1) * N.descFactorial Ds.length := by
      rw [Nat.descFactorial_succ, hk]
    have hDr : D r ∈ I ^ (k + 1) := hD.map_mem_pow I (k + 1) hrest
    have hmain : D (N.descFactorial Ds.length • (f ^ (k + 1) * pr)) -
        N.descFactorial (Ds.length + 1) • (f ^ k * (D f * pr)) =
          N.descFactorial Ds.length • (f ^ (k + 1) * D pr) := by
      rw [map_nsmul, hD, hD.map_pow_succ, hdesc, mul_nsmul']
      simp only [nsmul_eq_mul]
      ring
    have hfk : f ^ (k + 1) ∈ I ^ (k + 1) := Ideal.pow_mem_pow hf _
    simp only [List.prod_cons, List.map_cons, Module.End.mul_apply]
    rw [hprod, map_add]
    have : D r + D (N.descFactorial Ds.length • (f ^ (k + 1) * pr)) -
        N.descFactorial (Ds.length + 1) • (f ^ k * (D f * pr)) =
          D r + N.descFactorial Ds.length • (f ^ (k + 1) * D pr) := by
      rw [← hmain]; abel
    rw [this]
    refine Ideal.add_mem _ hDr ?_
    exact Submodule.smul_of_tower_mem _ _ (Ideal.mul_mem_right _ _ hfk)

variable {S : Type*} [CommRing S]

/-- A product of exactly `N` derivations applied to `fᴺ`, `f ∈ I`, evaluated by a ring map
killing `I`, is `N!` times the product of the evaluated first derivatives. -/
theorem IsLeibniz.eval_prod_apply_pow_of_length_eq (I : Ideal R) {f : R} (hf : f ∈ I)
    (ε : R →+* S) (hε : ∀ a ∈ I, ε a = 0) (Ds : List (Module.End K R))
    (hDs : ∀ D ∈ Ds, IsLeibniz D) (N : ℕ) (hN : Ds.length = N) :
    ε (Ds.prod (f ^ N)) = (N ! : S) * (Ds.map fun D => ε (D f)).prod := by
  have h := IsLeibniz.prod_apply_pow_sub_mem I hf Ds hDs N hN.le
  rw [hN, Nat.sub_self, zero_add, pow_one] at h
  have h0 := hε _ h
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, Nat.descFactorial_self, map_nsmul, pow_zero, one_mul, map_list_prod,
    List.map_map, nsmul_eq_mul]
  rfl

/-- A product of fewer than `N` derivations applied to `fᴺ`, `f ∈ I`, is killed by a ring map
killing `I`. -/
theorem IsLeibniz.eval_prod_apply_pow_of_length_lt (I : Ideal R) {f : R} (hf : f ∈ I)
    (ε : R →+* S) (hε : ∀ a ∈ I, ε a = 0) (Ds : List (Module.End K R))
    (hDs : ∀ D ∈ Ds, IsLeibniz D) (N : ℕ) (hN : Ds.length < N) :
    ε (Ds.prod (f ^ N)) = 0 := by
  have h := IsLeibniz.prod_apply_pow_sub_mem I hf Ds hDs N hN.le
  have hmem : Ds.prod (f ^ N) ∈ I := by
    have h1 : Ds.prod (f ^ N) - N.descFactorial Ds.length •
        (f ^ (N - Ds.length) * (Ds.map fun D => D f).prod) ∈ I :=
      Ideal.pow_le_self (by omega) h
    have h2 : N.descFactorial Ds.length •
        (f ^ (N - Ds.length) * (Ds.map fun D => D f).prod) ∈ I :=
      Submodule.smul_of_tower_mem _ _
        (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hf _ (by omega)))
    simpa using Ideal.add_mem _ h1 h2
  exact hε _ hmem

end Leibniz

/-! ## Words span the filtration -/

section Words

variable (K : Type*) [CommRing K] (L : Type*) [LieRing L] [LieAlgebra K L]

local notation "U" => UniversalEnvelopingAlgebra K L

/-- The span of the words of length at most `d`. -/
def wordSpan (d : ℕ) : Submodule K U :=
  Submodule.span K {u | ∃ l : List L, l.length ≤ d ∧ word K L l = u}

theorem word_mem_wordSpan {d : ℕ} (l : List L) (hl : l.length ≤ d) :
    word K L l ∈ wordSpan K L d :=
  Submodule.subset_span ⟨l, hl, rfl⟩

theorem wordSpan_mono {d e : ℕ} (h : d ≤ e) : wordSpan K L d ≤ wordSpan K L e :=
  Submodule.span_mono fun _ ⟨l, hl, hu⟩ => ⟨l, hl.trans h, hu⟩

theorem mul_generator_mem_wordSpan {d : ℕ} {u : U} (hu : u ∈ wordSpan K L d) (x : L) :
    u * UniversalEnvelopingAlgebra.ι K x ∈ wordSpan K L (d + 1) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    have : word K L l * UniversalEnvelopingAlgebra.ι K x = word K L (l ++ [x]) := by
      simp [word, List.map_append, List.prod_append]
    rw [this]
    exact word_mem_wordSpan K L _ (by simp; omega)
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu

theorem degreeFiltration_le_wordSpan (d : ℕ) : degreeFiltration K L d ≤ wordSpan K L d := by
  intro P hP
  induction hP using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    have : algebraMap K U r = r • word K L [] := by simp [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ r (word_mem_wordSpan K L [] (by simp))
  | add x y i _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul_mem i x _ hx m hm =>
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hm
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    obtain ⟨y, rfl⟩ := hy
    rw [mul_add]
    refine Submodule.add_mem _ ?_ (mul_generator_mem_wordSpan K L hx y)
    rw [← Algebra.commutes, ← Algebra.smul_def]
    exact Submodule.smul_mem _ r (wordSpan_mono K L (Nat.le_succ i) hx)

end Words

/-! ## The symbol map -/

section Symbol

variable (K : Type*) [Field K] [CharZero K] (L : Type*) [LieRing L] [LieAlgebra K L]
  (R : Type*) [CommRing R] [Algebra K R] (S : Type*) [CommRing S] [Algebra K S]

local notation "U" => UniversalEnvelopingAlgebra K L

/-- Data defining symbols: a representation of `L` on `R` by derivations, an ideal `𝔪`, an
algebra map `ε : R → S` killing `𝔪`, and an element `l ∈ 𝔪`. -/
structure SymbolData where
  /-- The representation by derivations. -/
  ρ : L →ₗ⁅K⁆ Module.End K R
  leibniz : ∀ x, IsLeibniz (ρ x)
  /-- The ideal of the base point. -/
  𝔪 : Ideal R
  /-- Evaluation at the base point. -/
  ε : R →ₐ[K] S
  ε_eq_zero : ∀ a ∈ 𝔪, ε a = 0
  /-- The element whose powers are differentiated. -/
  l : R
  l_mem : l ∈ 𝔪

variable {K L R S} (d : SymbolData K L R S)

namespace SymbolData

/-- The linear symbol of a Lie algebra element: `ξ(x) = ε(ρ(x) l)`. -/
def ξ : L →ₗ[K] S :=
  d.ε.toLinearMap ∘ₗ LinearMap.applyₗ d.l ∘ₗ d.ρ.toLinearMap

omit [CharZero K] in
theorem ξ_apply (x : L) : d.ξ x = d.ε (d.ρ x d.l) := rfl

/-- The degree-`N` symbol `σ_N(P) = ε(ρ(P) lᴺ) / N!`. -/
def symbol (N : ℕ) : U →ₗ[K] S :=
  ((N ! : K)⁻¹) • (d.ε.toLinearMap ∘ₗ LinearMap.applyₗ (d.l ^ N) ∘ₗ
    (UniversalEnvelopingAlgebra.lift K d.ρ).toLinearMap)

omit [CharZero K] in
theorem lift_word (l : List L) :
    UniversalEnvelopingAlgebra.lift K d.ρ (word K L l) = (l.map d.ρ).prod := by
  induction l with
  | nil => simp [word]
  | cons x l ih => rw [word_cons, map_mul, ih, UniversalEnvelopingAlgebra.lift_ι_apply]; rfl

theorem symbol_word_of_length_eq {N : ℕ} (l : List L) (hl : l.length = N) :
    d.symbol N (word K L l) = (l.map d.ξ).prod := by
  have hDs : ∀ D ∈ l.map d.ρ, IsLeibniz D := by
    intro D hD
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hD
    exact d.leibniz x
  have h := IsLeibniz.eval_prod_apply_pow_of_length_eq d.𝔪 d.l_mem d.ε.toRingHom d.ε_eq_zero
    (l.map d.ρ) hDs N (by simpa using hl)
  simp only [symbol, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply, lift_word]
  change (N ! : K)⁻¹ • d.ε.toRingHom ((l.map d.ρ).prod (d.l ^ N)) = _
  rw [h, List.map_map]
  have hN : (N ! : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  rw [Algebra.smul_def, ← mul_assoc, show (N ! : S) = algebraMap K S (N ! : K) by simp,
    ← map_mul, inv_mul_cancel₀ hN, map_one, one_mul]
  rfl

omit [CharZero K] in
theorem symbol_word_of_length_lt {N : ℕ} (l : List L) (hl : l.length < N) :
    d.symbol N (word K L l) = 0 := by
  have hDs : ∀ D ∈ l.map d.ρ, IsLeibniz D := by
    intro D hD
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hD
    exact d.leibniz x
  have h := IsLeibniz.eval_prod_apply_pow_of_length_lt d.𝔪 d.l_mem d.ε.toRingHom d.ε_eq_zero
    (l.map d.ρ) hDs N (by simpa using hl)
  simp only [symbol, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply, lift_word]
  change (N ! : K)⁻¹ • d.ε.toRingHom ((l.map d.ρ).prod (d.l ^ N)) = 0
  rw [h, smul_zero]

omit [CharZero K] in
/-- `σ_N` vanishes on `U_M` for `M < N`. -/
theorem symbol_eq_zero_of_mem {M N : ℕ} (hMN : M < N) {P : U}
    (hP : P ∈ degreeFiltration K L M) : d.symbol N P = 0 := by
  have hP' := degreeFiltration_le_wordSpan K L M hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    exact d.symbol_word_of_length_lt l (by omega)
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | smul c u _ hu => rw [map_smul, hu, smul_zero]

theorem symbol_word_mul_word {a b : ℕ} (l₁ l₂ : List L) (h₁ : l₁.length ≤ a)
    (h₂ : l₂.length ≤ b) :
    d.symbol (a + b) (word K L l₁ * word K L l₂) =
      d.symbol a (word K L l₁) * d.symbol b (word K L l₂) := by
  have hw : word K L l₁ * word K L l₂ = word K L (l₁ ++ l₂) := by
    simp [word, List.map_append, List.prod_append]
  rw [hw]
  rcases h₁.lt_or_eq with h₁ | h₁
  · rw [d.symbol_word_of_length_lt _ (by simp; omega), d.symbol_word_of_length_lt _ h₁,
      zero_mul]
  rcases h₂.lt_or_eq with h₂ | h₂
  · rw [d.symbol_word_of_length_lt _ (by simp; omega), d.symbol_word_of_length_lt _ h₂,
      mul_zero]
  rw [d.symbol_word_of_length_eq _ (by simp; omega), d.symbol_word_of_length_eq _ h₁,
    d.symbol_word_of_length_eq _ h₂, List.map_append, List.prod_append]

/-- Multiplicativity of symbols on `U_a × U_b`. -/
theorem symbol_mul {a b : ℕ} {P Q : U} (hP : P ∈ degreeFiltration K L a)
    (hQ : Q ∈ degreeFiltration K L b) :
    d.symbol (a + b) (P * Q) = d.symbol a P * d.symbol b Q := by
  have hP' := degreeFiltration_le_wordSpan K L a hP
  have hQ' := degreeFiltration_le_wordSpan K L b hQ
  clear hP hQ
  induction hP' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l₁, hl₁, rfl⟩ := hu
    induction hQ' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l₂, hl₂, rfl⟩ := hv
      exact d.symbol_word_mul_word l₁ l₂ hl₁ hl₂
    | zero => simp
    | add v w _ _ hv hw => rw [mul_add, map_add, map_add, hv, hw, mul_add]
    | smul c v _ hv => rw [mul_smul_comm, map_smul, map_smul, hv, mul_smul_comm]
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul, map_add, map_add, hu, hv, add_mul]
  | smul c u _ hu => rw [smul_mul_assoc, map_smul, map_smul, hu, smul_mul_assoc]

theorem symbol_one_ι (x : L) : d.symbol 1 (UniversalEnvelopingAlgebra.ι K x) = d.ξ x := by
  have h := d.symbol_word_of_length_eq [x] rfl
  simpa [word] using h

theorem symbol_zero_algebraMap (c : K) : d.symbol 0 (algebraMap K U c) = algebraMap K S c := by
  have h := d.symbol_word_of_length_eq (N := 0) [] rfl
  simp only [word_nil, List.map_nil, List.prod_nil] at h
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h, Algebra.algebraMap_eq_smul_one]

theorem symbol_word_commutator (x : L) (δ : Module.End K S) (hδ : IsLeibniz δ)
    (hδξ : ∀ y, δ (d.ξ y) = d.ξ ⁅x, y⁆) :
    ∀ (l : List L) (N : ℕ), l.length ≤ N →
      d.symbol N (UniversalEnvelopingAlgebra.ι K x * word K L l -
        word K L l * UniversalEnvelopingAlgebra.ι K x) = δ (d.symbol N (word K L l)) := by
  intro l
  induction l with
  | nil =>
    intro N _
    simp only [word_nil, mul_one, one_mul, sub_self, map_zero]
    rcases N with _ | N
    · have h := d.symbol_word_of_length_eq (N := 0) [] rfl
      simp only [word_nil, List.map_nil, List.prod_nil] at h
      rw [h]
      have h1 := hδ 1 1
      simp only [mul_one, one_mul] at h1
      have : δ 1 = 0 := by
        have h2 : δ 1 + δ 1 = δ 1 := by rw [← h1]
        simpa using h2
      rw [this]
    · have h := d.symbol_word_of_length_lt (N := N + 1) [] (by simp)
      simp only [word_nil] at h
      rw [h, map_zero]
  | cons y l ih =>
    intro N hN
    simp only [List.length_cons] at hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hcomm : UniversalEnvelopingAlgebra.ι K x * word K L (y :: l) -
        word K L (y :: l) * UniversalEnvelopingAlgebra.ι K x =
          word K L (⁅x, y⁆ :: l) + UniversalEnvelopingAlgebra.ι K y *
            (UniversalEnvelopingAlgebra.ι K x * word K L l -
              word K L l * UniversalEnvelopingAlgebra.ι K x) := by
      have hxy : UniversalEnvelopingAlgebra.ι K ⁅x, y⁆ =
          UniversalEnvelopingAlgebra.ι K x * UniversalEnvelopingAlgebra.ι K y -
            UniversalEnvelopingAlgebra.ι K y * UniversalEnvelopingAlgebra.ι K x :=
        (UniversalEnvelopingAlgebra.ι K).map_lie x y
      simp only [word_cons, hxy]
      noncomm_ring
    have hlow : UniversalEnvelopingAlgebra.ι K x * word K L l -
        word K L l * UniversalEnvelopingAlgebra.ι K x ∈ degreeFiltration K L M := by
      have := commutator_mem_degreeFiltration K L
        (show UniversalEnvelopingAlgebra.ι K x ∈ degreeFiltration K L 1 by
          simpa using generator_mem_degreeOne K L x)
        (degreeFiltration_mono K L (show l.length ≤ M by omega)
          (word_mem_degreeFiltration K L l))
      simpa using this
    have hy : UniversalEnvelopingAlgebra.ι K y ∈ degreeFiltration K L 1 := by
      simpa using generator_mem_degreeOne K L y
    have hsplit : ∀ (z : L) (Q : U), Q ∈ degreeFiltration K L M →
        d.symbol (M + 1) (UniversalEnvelopingAlgebra.ι K z * Q) = d.ξ z * d.symbol M Q := by
      intro z Q hQ
      have hz : UniversalEnvelopingAlgebra.ι K z ∈ degreeFiltration K L 1 := by
        simpa using generator_mem_degreeOne K L z
      rw [show M + 1 = 1 + M by omega, d.symbol_mul hz hQ, d.symbol_one_ι]
    have hwl : word K L l ∈ degreeFiltration K L M :=
      degreeFiltration_mono K L (show l.length ≤ M by omega) (word_mem_degreeFiltration K L l)
    have h1 : d.symbol (M + 1) (word K L (⁅x, y⁆ :: l)) = d.ξ ⁅x, y⁆ * d.symbol M (word K L l) := by
      rw [word_cons]; exact hsplit _ _ hwl
    have h2 : d.symbol (M + 1) (UniversalEnvelopingAlgebra.ι K y *
        (UniversalEnvelopingAlgebra.ι K x * word K L l -
          word K L l * UniversalEnvelopingAlgebra.ι K x)) =
          d.ξ y * δ (d.symbol M (word K L l)) := by
      rw [hsplit _ _ hlow, ih M (by omega)]
    have h3 : d.symbol (M + 1) (word K L (y :: l)) = d.ξ y * d.symbol M (word K L l) := by
      rw [word_cons]; exact hsplit _ _ hwl
    rw [hcomm, map_add, h1, h2, h3, hδ, hδξ]
    ring

/-- Commutators with `x ∈ L` act on symbols by any derivation `δ` of `S` with
`δ(ξ y) = ξ ⁅x, y⁆`. -/
theorem symbol_commutator (x : L) (δ : Module.End K S) (hδ : IsLeibniz δ)
    (hδξ : ∀ y, δ (d.ξ y) = d.ξ ⁅x, y⁆) {N : ℕ} {P : U}
    (hP : P ∈ degreeFiltration K L N) :
    d.symbol N (UniversalEnvelopingAlgebra.ι K x * P - P * UniversalEnvelopingAlgebra.ι K x) =
      δ (d.symbol N P) := by
  have hP' := degreeFiltration_le_wordSpan K L N hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    exact d.symbol_word_commutator x δ hδ hδξ l N hl
  | zero => simp
  | add u v _ _ hu hv =>
    rw [mul_add, add_mul, add_sub_add_comm, map_add, hu, hv, map_add, map_add]
  | smul c u _ hu =>
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, map_smul, hu, map_smul, map_smul]

end SymbolData

end Symbol

end Langlands.Archimedean.Kostant
