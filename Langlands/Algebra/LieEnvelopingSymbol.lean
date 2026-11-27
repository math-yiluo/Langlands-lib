import Langlands.Algebra.OrderedMonomialBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Symbols of enveloping elements through ordered PBW coordinates -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Algebra.LieEnvelopingSymbol

open Langlands.Algebra.UniversalEnveloping Langlands.Archimedean.Kostant
  Langlands.Archimedean.VermaPBW Langlands.Algebra.LieWeightProjection MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
  {I : Type w} [Fintype I] [DecidableEq I] (b : Module.Basis I k L) {bs : List I}
  (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs)

local notation "U" => UniversalEnvelopingAlgebra k L
local notation "ι" => UniversalEnvelopingAlgebra.ι k

/-- The coordinates of an enveloping element in the ordered PBW basis along `bs`, written as
a polynomial: the ordered monomial with exponent `α` goes to the monomial `X^α`. -/
def pbwPoly : U →ₗ[k] MvPolynomial I k :=
  (orderedMonomialBasis b hbs hall).constr k fun α => monomial α 1

theorem pbwPoly_orderedMonomial (α : I →₀ ℕ) :
    pbwPoly b hbs hall (orderedMonomial k L b bs α) = monomial α 1 := by
  rw [← orderedMonomialBasis_apply b hbs hall, pbwPoly, Module.Basis.constr_basis]

theorem coeff_pbwPoly (P : U) (α : I →₀ ℕ) :
    (pbwPoly b hbs hall P).coeff α = (orderedMonomialBasis b hbs hall).repr P α := by
  let B := orderedMonomialBasis b hbs hall
  have h : lcoeff k α ∘ₗ pbwPoly b hbs hall = B.coord α := by
    refine B.ext fun β => ?_
    rw [LinearMap.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      orderedMonomialBasis_apply, pbwPoly_orderedMonomial, lcoeff_apply, coeff_monomial,
      Finsupp.single_apply]
  exact LinearMap.congr_fun h P

/-- An element of the degree filtration `U_N` has PBW coordinates only in degrees at most
`N`. -/
theorem coeff_pbwPoly_eq_zero_of_mem {N : ℕ} {P : U} (hP : P ∈ degreeFiltration k L N)
    {α : I →₀ ℕ} (hα : N < α.degree) : (pbwPoly b hbs hall P).coeff α = 0 := by
  have hP' := degreeFiltration_le_orderedSpan k L b hbs hall N hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨β, hβ, rfl⟩ := hu
    have hβ' : β.degree ≤ N := hβ
    rw [pbwPoly_orderedMonomial, coeff_monomial, ite_eq_right]
    rintro rfl
    exact absurd hβ' (not_le.mpr hα)
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

/-- The degree-`N` symbol: the homogeneous component of degree `N` of the PBW coordinate
polynomial. -/
def symbol (N : ℕ) : U →ₗ[k] MvPolynomial I k :=
  homogeneousComponent N ∘ₗ pbwPoly b hbs hall

theorem coeff_symbol (N : ℕ) (P : U) (α : I →₀ ℕ) :
    (symbol b hbs hall N P).coeff α =
      if α.degree = N then (orderedMonomialBasis b hbs hall).repr P α else 0 := by
  rw [symbol, LinearMap.comp_apply, coeff_homogeneousComponent, coeff_pbwPoly]

theorem symbol_orderedMonomial (N : ℕ) (α : I →₀ ℕ) :
    symbol b hbs hall N (orderedMonomial k L b bs α) =
      if α.degree = N then monomial α 1 else 0 := by
  ext β
  rw [coeff_symbol, ← orderedMonomialBasis_apply b hbs hall, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases hαβ : α = β
  · subst hαβ
    by_cases h : α.degree = N <;> simp [h]
  · by_cases h : α.degree = N <;> simp [h, hαβ, coeff_monomial]

/-- `σ_N` vanishes on `U_M` for `M < N`. -/
theorem symbol_eq_zero_of_mem {M N : ℕ} (hMN : M < N) {P : U}
    (hP : P ∈ degreeFiltration k L M) : symbol b hbs hall N P = 0 := by
  ext α
  rw [coeff_symbol]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with h
  · rw [← coeff_pbwPoly]
    exact coeff_pbwPoly_eq_zero_of_mem b hbs hall hP (h ▸ hMN)
  · rfl

omit [Fintype I] in
private theorem toFinsupp_cons_expand (c : I) (α : I →₀ ℕ)
    (hα : ((expand bs α : List I) : Multiset I) = Finsupp.toMultiset α) :
    Multiset.toFinsupp ((c :: expand bs α : List I) : Multiset I) = α + Finsupp.single c 1 := by
  rw [Multiset.toFinsupp_eq_iff, ← Multiset.cons_coe, hα, map_add,
    Finsupp.toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]

/-- Multiplying by a basis generator multiplies the symbol by the corresponding variable. -/
theorem symbol_generator_mul (c : I) {M : ℕ} {P : U} (hP : P ∈ degreeFiltration k L M) :
    symbol b hbs hall (M + 1) (ι (b c) * P) = X c * symbol b hbs hall M P := by
  have hP' := degreeFiltration_le_orderedSpan k L b hbs hall M hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, hα, rfl⟩ := hu
    have hα : α.degree ≤ M := hα
    have hw : ι (b c) * orderedMonomial k L b bs α = word k L ((c :: expand bs α).map b) := by
      rw [orderedMonomial, List.map_cons, word_cons]
    have hlen : (c :: expand bs α).length = α.degree + 1 := by
      rw [List.length_cons, length_expand hbs hall]
    rcases hα.lt_or_eq with hlt | heq
    · have h1 : ι (b c) * orderedMonomial k L b bs α ∈ degreeFiltration k L M := by
        rw [hw]
        refine degreeFiltration_mono k L ?_ (word_mem_degreeFiltration k L _)
        rw [List.length_map, hlen]
        omega
      rw [symbol_eq_zero_of_mem b hbs hall (Nat.lt_succ_self M) h1, symbol_orderedMonomial,
        ite_eq_right (Nat.ne_of_lt hlt), mul_zero]
    · set α' := α + Finsupp.single c 1 with hα'
      have hperm : (c :: expand bs α).Perm (expand bs α') := by
        have h := perm_expand hbs hall (c :: expand bs α)
        rwa [toFinsupp_cons_expand c α (coe_expand hbs hall α)] at h
      have hdiff := word_sub_word_mem_of_perm k L (hperm.map b)
      rw [List.length_map, hlen, Nat.add_sub_cancel, heq] at hdiff
      have hdeg : α'.degree = M + 1 := by
        rw [hα', map_add, Finsupp.degree_single, heq]
      have hsplit : ι (b c) * orderedMonomial k L b bs α =
          (word k L ((c :: expand bs α).map b) - word k L ((expand bs α').map b)) +
            orderedMonomial k L b bs α' := by
        rw [hw, orderedMonomial, sub_add_cancel]
      rw [hsplit, map_add, symbol_eq_zero_of_mem b hbs hall (Nat.lt_succ_self M) hdiff,
        zero_add, symbol_orderedMonomial, ite_eq_left hdeg, symbol_orderedMonomial, ite_eq_left heq, X,
        monomial_mul_monomial, one_mul, hα', add_comm]
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, map_add, hu, hv, map_add, mul_add]
  | smul t u _ hu => rw [mul_smul_comm, map_smul, hu, map_smul, mul_smul_comm]

/-- The linear symbol of a Lie algebra element: its basis coordinates as a linear form. -/
def ξ : L →ₗ[k] MvPolynomial I k := b.constr k X

omit [Fintype I] [DecidableEq I] in
@[simp]
theorem ξ_basis (c : I) : ξ b (b c) = X c := b.constr_basis _ _ _

omit [DecidableEq I] in
theorem ξ_apply (x : L) : ξ b x = ∑ c, b.repr x c • X c := by
  rw [ξ, Module.Basis.constr_apply_fintype]
  rfl

/-- Multiplying by a Lie generator multiplies the symbol by its linear symbol. -/
theorem symbol_ι_mul (x : L) {M : ℕ} {P : U} (hP : P ∈ degreeFiltration k L M) :
    symbol b hbs hall (M + 1) (ι x * P) = ξ b x * symbol b hbs hall M P := by
  have h : symbol b hbs hall (M + 1) ∘ₗ LinearMap.mulRight k P ∘ₗ
      (UniversalEnvelopingAlgebra.ι k (L := L)).toLinearMap =
        LinearMap.mulRight k (symbol b hbs hall M P) ∘ₗ ξ b := by
    refine b.ext fun c => ?_
    simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, LinearMap.mulRight_apply, ξ_basis]
    exact symbol_generator_mul b hbs hall c hP
  exact LinearMap.congr_fun h x

theorem symbol_word_of_length_lt {N : ℕ} (l : List L) (hl : l.length < N) :
    symbol b hbs hall N (word k L l) = 0 :=
  symbol_eq_zero_of_mem b hbs hall hl (word_mem_degreeFiltration k L l)

theorem symbol_one : symbol b hbs hall 0 (1 : U) = 1 := by
  have h := symbol_orderedMonomial b hbs hall 0 0
  rw [ite_eq_left (by simp)] at h
  simpa [orderedMonomial, expand_zero, word] using h

theorem symbol_word_of_length_eq (l : List L) :
    symbol b hbs hall l.length (word k L l) = (l.map (ξ b)).prod := by
  induction l with
  | nil => simpa [word] using symbol_one b hbs hall
  | cons x l ih =>
    rw [word_cons, List.length_cons, symbol_ι_mul b hbs hall x (word_mem_degreeFiltration k L l),
      ih, List.map_cons, List.prod_cons]

theorem symbol_word_of_length_eq' {N : ℕ} (l : List L) (hl : l.length = N) :
    symbol b hbs hall N (word k L l) = (l.map (ξ b)).prod := by
  subst hl
  exact symbol_word_of_length_eq b hbs hall l

theorem symbol_word_mul_word {a c : ℕ} (l₁ l₂ : List L) (h₁ : l₁.length ≤ a)
    (h₂ : l₂.length ≤ c) :
    symbol b hbs hall (a + c) (word k L l₁ * word k L l₂) =
      symbol b hbs hall a (word k L l₁) * symbol b hbs hall c (word k L l₂) := by
  have hw : word k L l₁ * word k L l₂ = word k L (l₁ ++ l₂) := by
    simp [word, List.map_append, List.prod_append]
  rw [hw]
  rcases h₁.lt_or_eq with h₁ | h₁
  · rw [symbol_word_of_length_lt b hbs hall _ (by simp; omega),
      symbol_word_of_length_lt b hbs hall _ h₁, zero_mul]
  rcases h₂.lt_or_eq with h₂ | h₂
  · rw [symbol_word_of_length_lt b hbs hall _ (by simp; omega),
      symbol_word_of_length_lt b hbs hall _ h₂, mul_zero]
  rw [symbol_word_of_length_eq' b hbs hall _ (by simp; omega),
    symbol_word_of_length_eq' b hbs hall _ h₁, symbol_word_of_length_eq' b hbs hall _ h₂,
    List.map_append, List.prod_append]

/-- Multiplicativity of symbols on `U_a × U_c`. -/
theorem symbol_mul {a c : ℕ} {P Q : U} (hP : P ∈ degreeFiltration k L a)
    (hQ : Q ∈ degreeFiltration k L c) :
    symbol b hbs hall (a + c) (P * Q) = symbol b hbs hall a P * symbol b hbs hall c Q := by
  have hP' := degreeFiltration_le_wordSpan k L a hP
  have hQ' := degreeFiltration_le_wordSpan k L c hQ
  clear hP hQ
  induction hP' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l₁, hl₁, rfl⟩ := hu
    induction hQ' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l₂, hl₂, rfl⟩ := hv
      exact symbol_word_mul_word b hbs hall l₁ l₂ hl₁ hl₂
    | zero => simp
    | add v w _ _ hv hw => rw [mul_add, map_add, map_add, hv, hw, mul_add]
    | smul t v _ hv => rw [mul_smul_comm, map_smul, map_smul, hv, mul_smul_comm]
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul, map_add, map_add, hu, hv, add_mul]
  | smul t u _ hu => rw [smul_mul_assoc, map_smul, map_smul, hu, smul_mul_assoc]

/-- Commutators with `x ∈ L` act on symbols by any derivation `δ` with
`δ(ξ y) = ξ ⁅x, y⁆`. -/
theorem symbol_word_commutator (x : L) (δ : Derivation k (MvPolynomial I k) (MvPolynomial I k))
    (hδξ : ∀ y, δ (ξ b y) = ξ b ⁅x, y⁆) :
    ∀ (l : List L) (N : ℕ), l.length ≤ N →
      symbol b hbs hall N (ι x * word k L l - word k L l * ι x) =
        δ (symbol b hbs hall N (word k L l)) := by
  intro l
  induction l with
  | nil =>
    intro N _
    simp only [word_nil, mul_one, one_mul, sub_self, map_zero]
    rcases N with _ | N
    · rw [symbol_one, Derivation.map_one_eq_zero]
    · have h := symbol_word_of_length_lt b hbs hall (N := N + 1) [] (by simp)
      simp only [word_nil] at h
      rw [h, map_zero]
  | cons y l ih =>
    intro N hN
    simp only [List.length_cons] at hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hcomm : ι x * word k L (y :: l) - word k L (y :: l) * ι x =
        word k L (⁅x, y⁆ :: l) + ι y * (ι x * word k L l - word k L l * ι x) := by
      have hxy : ι ⁅x, y⁆ = ι x * ι y - ι y * ι x :=
        (UniversalEnvelopingAlgebra.ι k).map_lie x y
      simp only [word_cons, hxy]
      noncomm_ring
    have hwl : word k L l ∈ degreeFiltration k L M :=
      degreeFiltration_mono k L (show l.length ≤ M by omega) (word_mem_degreeFiltration k L l)
    have hlow : ι x * word k L l - word k L l * ι x ∈ degreeFiltration k L M := by
      have := commutator_mem_degreeFiltration k L
        (show ι x ∈ degreeFiltration k L 1 by simpa using generator_mem_degreeOne k L x) hwl
      simpa using this
    rw [hcomm, map_add, word_cons, symbol_ι_mul b hbs hall _ hwl,
      symbol_ι_mul b hbs hall _ hlow, ih M (by omega), word_cons,
      symbol_ι_mul b hbs hall _ hwl, Derivation.leibniz, hδξ, smul_eq_mul, smul_eq_mul]
    ring

theorem symbol_commutator (x : L) (δ : Derivation k (MvPolynomial I k) (MvPolynomial I k))
    (hδξ : ∀ y, δ (ξ b y) = ξ b ⁅x, y⁆) {N : ℕ} {P : U}
    (hP : P ∈ degreeFiltration k L N) :
    symbol b hbs hall N (ι x * P - P * ι x) = δ (symbol b hbs hall N P) := by
  have hP' := degreeFiltration_le_wordSpan k L N hP
  clear hP
  induction hP' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨l, hl, rfl⟩ := hu
    exact symbol_word_commutator b hbs hall x δ hδξ l N hl
  | zero => simp
  | add u v _ _ hu hv =>
    rw [mul_add, add_mul, add_sub_add_comm, map_add, hu, hv, map_add, map_add]
  | smul t u _ hu =>
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, map_smul, hu, map_smul, Derivation.map_smul]

/-- An element of `U_{N+1}` whose degree-`(N+1)` symbol vanishes lies in `U_N`. -/
theorem mem_degreeFiltration_of_symbol_eq_zero {N : ℕ} {P : U}
    (hP : P ∈ degreeFiltration k L (N + 1)) (h0 : symbol b hbs hall (N + 1) P = 0) :
    P ∈ degreeFiltration k L N := by
  let B := orderedMonomialBasis b hbs hall
  rw [← B.linearCombination_repr P, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  have hne : B.repr P α ≠ 0 := Finsupp.mem_support_iff.mp hα
  have hle : α.degree ≤ N := by
    by_contra hlt
    rcases Nat.lt_or_ge (N + 1) α.degree with h | h
    · exact hne (by rw [← coeff_pbwPoly]; exact coeff_pbwPoly_eq_zero_of_mem b hbs hall hP h)
    · replace h : α.degree = N + 1 := by omega
      have hc := congrArg (fun p => p.coeff α) h0
      simp only [coeff_symbol, h, ite_true] at hc
      exact hne (by simpa using hc)
  rw [orderedMonomialBasis_apply]
  exact degreeFiltration_mono k L hle (orderedMonomial_mem_degreeFiltration k L b hbs hall α)

/-- An element of `U_0` with vanishing degree-`0` symbol is zero. -/
theorem eq_zero_of_mem_zero_of_symbol_eq_zero {P : U} (hP : P ∈ degreeFiltration k L 0)
    (h0 : symbol b hbs hall 0 P = 0) : P = 0 := by
  let B := orderedMonomialBasis b hbs hall
  apply B.repr.injective
  ext α
  rw [map_zero, Finsupp.zero_apply]
  rcases Nat.eq_zero_or_pos α.degree with h | h
  · have hc := congrArg (fun p => p.coeff α) h0
    simp only [coeff_symbol, h, ite_true] at hc
    simpa using hc
  · rw [← coeff_pbwPoly]
    exact coeff_pbwPoly_eq_zero_of_mem b hbs hall hP h

/-- The derivation of the polynomial ring induced by the adjoint action of `y`:
`X_c ↦ ξ ⁅y, b c⁆`. -/
def adDer (y : L) : Derivation k (MvPolynomial I k) (MvPolynomial I k) :=
  mkDerivation k fun c => ξ b ⁅y, b c⁆

omit [Fintype I] [DecidableEq I] in
theorem adDer_X (y : L) (c : I) : adDer b y (X c) = ξ b ⁅y, b c⁆ :=
  mkDerivation_X k _ c

omit [Fintype I] [DecidableEq I] in
theorem adDer_ξ (y z : L) : adDer b y (ξ b z) = ξ b ⁅y, z⁆ := by
  have h : (adDer b y).toLinearMap ∘ₗ ξ b = ξ b ∘ₗ (LieModule.toEnd k L L y) := by
    refine b.ext fun c => ?_
    simp [adDer_X]
  exact LinearMap.congr_fun h z

/-- The symbol of a commutator `⁅y, P⁆` is the image of the symbol of `P` under `adDer y`. -/
theorem symbol_commutator_adDer (y : L) {N : ℕ} {P : U} (hP : P ∈ degreeFiltration k L N) :
    symbol b hbs hall N (ι y * P - P * ι y) = adDer b y (symbol b hbs hall N P) :=
  symbol_commutator b hbs hall y (adDer b y) (adDer_ξ b y) hP

end Langlands.Algebra.LieEnvelopingSymbol
