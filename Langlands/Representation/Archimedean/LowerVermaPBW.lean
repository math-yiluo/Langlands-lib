import Langlands.Representation.Archimedean.Kostant.AssocSymbol
import Langlands.Representation.Archimedean.LowerVerma
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Langlands.Representation.Archimedean.BGChaseCore

/-!
# Poincaré–Birkhoff–Witt for `U(𝔤𝔩_n(ℂ))` and lower Verma modules

See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaPBW

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping MvPolynomial Kostant

/-! ## Ordered monomials form a basis -/

section Generic

variable {K : Type*} [Field K] [CharZero K] {L : Type*} [LieRing L] [LieAlgebra K L]
  {B : Type*} [Fintype B] [DecidableEq B] (b : Module.Basis B K L) {bs : List B}
  {R : Type*} [CommRing R] [Algebra K R]

/-- If the degree-`N` part of a combination of ordered monomials of degree at most `N` vanishes
under the symbol, its coefficients of degree exactly `N` vanish. -/
theorem coeff_eq_zero_of_degree_eq (d : SymbolData K L R (MvPolynomial B K))
    (hξ : ∀ c, d.ξ (b c) = X c) (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) {N : ℕ}
    (c : (B →₀ ℕ) →₀ K) (hc : ∀ α ∈ c.support, α.degree ≤ N)
    (h0 : Finsupp.linearCombination K (orderedMonomial K L b bs) c = 0)
    {α : B →₀ ℕ} (hα : α.degree = N) : c α = 0 := by
  by_contra hne
  have hαs : α ∈ c.support := Finsupp.mem_support_iff.mpr hne
  have hcoeff := congrArg (fun P => lcoeff K α (d.symbol N P)) h0
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_zero, map_sum, map_sum,
    Finset.sum_eq_single α] at hcoeff
  · rw [map_smul, map_smul, symbol_orderedMonomial K L b d hξ hbs hall (hc α hαs),
      ite_eq_left hα, lcoeff_apply, coeff_monomial, ite_eq_left rfl, smul_eq_mul, mul_one] at hcoeff
    exact hne hcoeff
  · intro β hβ hβα
    rw [map_smul, map_smul, symbol_orderedMonomial K L b d hξ hbs hall (hc β hβ)]
    split_ifs
    · rw [lcoeff_apply, coeff_monomial, ite_eq_right hβα, smul_zero]
    · simp
  · intro h; exact absurd hαs h

/-- The ordered monomials are linearly independent. -/
theorem linearIndependent_orderedMonomial (d : SymbolData K L R (MvPolynomial B K))
    (hξ : ∀ c, d.ξ (b c) = X c) (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) :
    LinearIndependent K (orderedMonomial K L b bs) := by
  rw [linearIndependent_iff]
  suffices H : ∀ N, ∀ c : (B →₀ ℕ) →₀ K, (∀ α ∈ c.support, α.degree ≤ N) →
      Finsupp.linearCombination K (orderedMonomial K L b bs) c = 0 → c = 0 by
    intro c hc
    exact H (c.support.sup Finsupp.degree) c (fun α hα => Finset.le_sup hα) hc
  intro N
  induction N with
  | zero =>
    intro c hc h0
    ext α
    by_contra hne
    have hαs : α ∈ c.support := Finsupp.mem_support_iff.mpr hne
    exact hne (coeff_eq_zero_of_degree_eq b d hξ hbs hall c hc h0 (by have := hc α hαs; omega))
  | succ N ih =>
    intro c hc h0
    refine ih c (fun α hα => ?_) h0
    have h1 := hc α hα
    rcases Nat.lt_or_ge α.degree (N + 1) with h | h
    · omega
    · exact absurd (coeff_eq_zero_of_degree_eq b d hξ hbs hall c hc h0 (by omega))
        (Finsupp.mem_support_iff.mp hα)

omit [CharZero K] in
/-- The ordered monomials span `U(L)`. -/
theorem top_le_span_orderedMonomial (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) :
    ⊤ ≤ Submodule.span K (Set.range (orderedMonomial K L b bs)) := by
  intro u _
  obtain ⟨N, hN⟩ := exists_mem_degreeFiltration K L u
  exact Submodule.span_mono (Set.image_subset_range _ _)
    (degreeFiltration_le_orderedSpan K L b hbs hall N hN)

/-- The Poincaré–Birkhoff–Witt basis of ordered monomials. -/
def pbwBasis (d : SymbolData K L R (MvPolynomial B K)) (hξ : ∀ c, d.ξ (b c) = X c)
    (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) :
    Module.Basis (B →₀ ℕ) K (UniversalEnvelopingAlgebra K L) :=
  Module.Basis.mk (linearIndependent_orderedMonomial b d hξ hbs hall)
    (top_le_span_orderedMonomial b hbs hall)

theorem pbwBasis_apply (d : SymbolData K L R (MvPolynomial B K)) (hξ : ∀ c, d.ξ (b c) = X c)
    (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (α : B →₀ ℕ) :
    pbwBasis b d hξ hbs hall α = orderedMonomial K L b bs α :=
  Module.Basis.mk_apply _ _ _

end Generic

/-! ## Lists of indices -/

section Lists

variable {B : Type*}

theorem expand_append (l₁ l₂ : List B) (α : B →₀ ℕ) :
    expand (l₁ ++ l₂) α = expand l₁ α ++ expand l₂ α := by
  simp [expand, List.flatMap_append]

theorem expand_congr {l : List B} {α β : B →₀ ℕ} (h : ∀ c ∈ l, α c = β c) :
    expand l α = expand l β := by
  unfold expand
  exact List.flatMap_congr fun c hc => by rw [h c hc]

theorem expand_map {C : Type*} (f : C → B) (l : List C) (α : B →₀ ℕ)
    (γ : C →₀ ℕ) (h : ∀ c ∈ l, α (f c) = γ c) :
    expand (l.map f) α = (expand l γ).map f := by
  unfold expand
  rw [List.flatMap_map, List.map_flatMap]
  exact List.flatMap_congr fun c hc => by rw [h c hc, List.map_replicate]

theorem expand_zero (l : List B) : expand l 0 = [] := by
  simp [expand]

theorem mem_expand {l : List B} {α : B →₀ ℕ} {c : B} (hc : c ∈ expand l α) : c ∈ l := by
  unfold expand at hc
  obtain ⟨d, hd, hcd⟩ := List.mem_flatMap.mp hc
  rw [List.eq_of_mem_replicate hcd]
  exact hd

end Lists

theorem word_append {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L]
    (l₁ l₂ : List L) : word K L (l₁ ++ l₂) = word K L l₁ * word K L l₂ := by
  simp [word, List.map_append, List.prod_append]

/-! ## The ordered basis of `U(𝔤𝔩_n(ℂ))` -/

section GLn

variable (n : ℕ)

/-- Indices `(p, q)` of the matrix units. -/
abbrev Idx := Fin n × Fin n

/-- The matrix unit `E_c`. -/
def unitE (c : Idx n) : Matrix (Fin n) (Fin n) ℂ := Matrix.single c.1 c.2 1

/-- Strictly upper indices `p < q`. -/
abbrev UpIdx := {c : Idx n // c.1 < c.2}

/-- Lower indices `q ≤ p` (diagonal included). -/
abbrev LoIdx := {c : Idx n // ¬ c.1 < c.2}

/-- An enumeration of the upper indices. -/
def upList : List (UpIdx n) := Finset.univ.toList

/-- An enumeration of the lower indices. -/
def loList : List (LoIdx n) := Finset.univ.toList

/-- The order of the basis: strictly upper indices first, then the lower ones. -/
def bsList : List (Idx n) := (upList n).map Subtype.val ++ (loList n).map Subtype.val

theorem upList_nodup : (upList n).Nodup := Finset.nodup_toList _

theorem loList_nodup : (loList n).Nodup := Finset.nodup_toList _

theorem mem_upList (c : UpIdx n) : c ∈ upList n := Finset.mem_toList.mpr (Finset.mem_univ _)

theorem mem_loList (c : LoIdx n) : c ∈ loList n := Finset.mem_toList.mpr (Finset.mem_univ _)

theorem bsList_nodup : (bsList n).Nodup := by
  refine List.nodup_append.mpr ⟨(upList_nodup n).map Subtype.val_injective,
    (loList_nodup n).map Subtype.val_injective, ?_⟩
  intro a ha b hb hab
  obtain ⟨a', -, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b', -, rfl⟩ := List.mem_map.mp hb
  exact b'.2 (hab ▸ a'.2)

theorem mem_bsList (c : Idx n) : c ∈ bsList n := by
  by_cases h : c.1 < c.2
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨⟨c, h⟩, mem_upList n _, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨c, h⟩, mem_loList n _, rfl⟩)

/-- The standard basis of matrix units. -/
def stdB : Module.Basis (Idx n) ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.stdBasis ℂ (Fin n) (Fin n)

theorem stdB_apply (c : Idx n) : stdB n c = unitE n c := by
  rw [stdB, unitE, ← Matrix.stdBasis_eq_single]

/-- The Poincaré–Birkhoff–Witt basis `E^α` of `U(𝔤𝔩_n(ℂ))` for the order `bsList`. -/
def basisU : Module.Basis (Idx n →₀ ℕ) ℂ (VermaGL.glU n) :=
  pbwBasis (stdB n) (AssocSymbol.symbolData (stdB n)) (AssocSymbol.symbolData_ξ_basis _)
    (bsList_nodup n) (mem_bsList n)

/-- The word `E_{c₁} ⋯ E_{c_k}` of a list of indices. -/
def W (l : List (Idx n)) : VermaGL.glU n :=
  word ℂ (Matrix (Fin n) (Fin n) ℂ) (l.map (stdB n))

theorem W_nil : W n [] = 1 := rfl

theorem W_cons (c : Idx n) (l : List (Idx n)) :
    W n (c :: l) = UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * W n l := by
  rw [W, List.map_cons, word_cons, stdB_apply]; rfl

theorem W_append (l₁ l₂ : List (Idx n)) : W n (l₁ ++ l₂) = W n l₁ * W n l₂ := by
  rw [W, List.map_append, word_append]; rfl

theorem basisU_apply (α : Idx n →₀ ℕ) : basisU n α = W n (expand (bsList n) α) := by
  rw [basisU, pbwBasis_apply]; rfl

/-- `E^α = E^{α⁺} E^{α⁻}`: the ordered monomial splits into its upper and lower parts. -/
theorem basisU_apply_split (α : Idx n →₀ ℕ) :
    basisU n α = W n (expand ((upList n).map Subtype.val) α) *
      W n (expand ((loList n).map Subtype.val) α) := by
  rw [basisU_apply, bsList, expand_append, W_append]

/-! ## Triangular subalgebras -/

section Sub

variable (P : Fin n → Fin n → Prop) [DecidableRel P] (hP : ∀ i k j, P i k → P k j → P i j)

/-- The Lie subalgebra of matrices supported on the positions `(i, j)` with `P i j`, for a
transitive relation `P`. -/
def subalg : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | ∀ i j, ¬ P i j → X i j = 0}
  add_mem' := by
    intro X Y hX hY i j h
    simp [hX i j h, hY i j h]
  zero_mem' := by
    intro i j _
    rfl
  smul_mem' := by
    intro c X hX i j h
    simp [hX i j h]
  lie_mem' := by
    intro X Y hX hY i j h
    have hk : ∀ k, X i k * Y k j = 0 ∧ Y i k * X k j = 0 := by
      intro k
      by_cases h1 : P i k
      · have h2 : ¬ P k j := fun h2 => h (hP i k j h1 h2)
        exact ⟨by rw [hY k j h2, mul_zero], by rw [hX k j h2, mul_zero]⟩
      · exact ⟨by rw [hX i k h1, zero_mul], by rw [hY i k h1, zero_mul]⟩
    rw [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp [hk]

theorem mem_subalg {X : Matrix (Fin n) (Fin n) ℂ} :
    X ∈ subalg n P hP ↔ ∀ i j, ¬ P i j → X i j = 0 := Iff.rfl

theorem unitE_mem_subalg (c : {c : Idx n // P c.1 c.2}) : unitE n c.1 ∈ subalg n P hP := by
  intro i j h
  rw [unitE, Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd c.2 h
  · rfl

/-- Coordinates on the subalgebra. -/
def subEquiv : subalg n P hP ≃ₗ[ℂ] ({c : Idx n // P c.1 c.2} → ℂ) where
  toFun X c := (X : Matrix (Fin n) (Fin n) ℂ) c.1.1 c.1.2
  map_add' X Y := by ext c; simp
  map_smul' a X := by ext c; simp
  invFun f := ⟨∑ c, f c • unitE n c.1,
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (unitE_mem_subalg n P hP c)⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    simp only [unitE]
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases h : P i j
    · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
      · simp
      · intro c _ hc
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        exact hc (Subtype.ext (Prod.ext h1 h2))
      · simp
    · rw [X.2 i j h]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [ite_eq_right]
      rintro ⟨rfl, rfl⟩
      exact h c.2
  right_inv f := by
    ext c
    change (∑ d, f d • unitE n d.1) c.1.1 c.1.2 = f c
    simp only [unitE]
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact hd (Subtype.ext (Prod.ext h1 h2))
    · simp

/-- The basis of matrix units of the subalgebra. -/
def subBasis : Module.Basis {c : Idx n // P c.1 c.2} ℂ (subalg n P hP) :=
  Module.Basis.ofEquivFun (subEquiv n P hP)

theorem coe_subBasis (c : {c : Idx n // P c.1 c.2}) :
    ((subBasis n P hP c : subalg n P hP) : Matrix (Fin n) (Fin n) ℂ) = unitE n c.1 := by
  classical
  rw [subBasis, Module.Basis.coe_ofEquivFun]
  dsimp only
  change ∑ d, (Pi.single c (1 : ℂ) : {c : Idx n // P c.1 c.2} → ℂ) d • unitE n d.1 = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro d _ hd
    rw [Pi.single_eq_of_ne hd, zero_smul]
  · simp

/-- The inclusion `U(𝔰) → U(𝔤𝔩_n)`. -/
def subInc : UniversalEnvelopingAlgebra ℂ (subalg n P hP) →ₐ[ℂ] VermaGL.glU n :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp (subalg n P hP).incl)

theorem subInc_ι (X : subalg n P hP) :
    subInc n P hP (UniversalEnvelopingAlgebra.ι ℂ X) =
      UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ) := by
  rw [subInc, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

theorem subInc_word (l : List {c : Idx n // P c.1 c.2}) :
    subInc n P hP (word ℂ (subalg n P hP) (l.map (subBasis n P hP))) = W n (l.map Subtype.val) := by
  induction l with
  | nil => simp [W]
  | cons c l ih =>
    rw [List.map_cons, word_cons, map_mul, ih, subInc_ι, coe_subBasis, List.map_cons, W_cons]

/-- The character of `U(𝔰)` defined by a character `μ` of `𝔰`. -/
def subChar (μ : subalg n P hP →ₗ⁅ℂ⁆ ℂ) : UniversalEnvelopingAlgebra ℂ (subalg n P hP) →ₐ[ℂ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℂ μ

theorem subChar_ι (μ : subalg n P hP →ₗ⁅ℂ⁆ ℂ) (X : subalg n P hP) :
    subChar n P hP μ (UniversalEnvelopingAlgebra.ι ℂ X) = μ X := by
  rw [subChar, UniversalEnvelopingAlgebra.lift_ι_apply]

theorem subChar_word (μ : subalg n P hP →ₗ⁅ℂ⁆ ℂ) (l : List {c : Idx n // P c.1 c.2}) :
    subChar n P hP μ (word ℂ (subalg n P hP) (l.map (subBasis n P hP))) =
      (l.map fun c => μ (subBasis n P hP c)).prod := by
  induction l with
  | nil => simp
  | cons c l ih => rw [List.map_cons, word_cons, map_mul, ih, subChar_ι, List.map_cons,
      List.prod_cons]

/-- The ordered monomials of `U(𝔰)` span it. -/
theorem top_le_span_subMonomial (l : List {c : Idx n // P c.1 c.2}) (hl : l.Nodup)
    (hall : ∀ c, c ∈ l) :
    ⊤ ≤ Submodule.span ℂ (Set.range (orderedMonomial ℂ (subalg n P hP) (subBasis n P hP) l)) :=
  top_le_span_orderedMonomial (subBasis n P hP) hl hall

end Sub

/-! ## The upper and lower triangular subalgebras -/

theorem up_trans : ∀ i k j : Fin n, i < k → k < j → i < j := fun _ _ _ => lt_trans

theorem lo_trans : ∀ i k j : Fin n, ¬ i < k → ¬ k < j → ¬ i < j := by
  intro i k j h1 h2
  rw [not_lt] at h1 h2 ⊢
  exact le_trans h2 h1

/-- The strictly upper triangular subalgebra `𝔫⁺`. -/
abbrev nUp := subalg n (fun i j => i < j) (up_trans n)

/-- The lower triangular subalgebra `𝔟⁻`. -/
abbrev bLo := subalg n (fun i j => ¬ i < j) (lo_trans n)

/-- The ordered monomial `E^β` of `U(𝔫⁺)`. -/
abbrev monoUp (β : UpIdx n →₀ ℕ) : UniversalEnvelopingAlgebra ℂ (nUp n) :=
  orderedMonomial ℂ (nUp n) (subBasis n _ (up_trans n)) (upList n) β

/-- The ordered monomial `E^γ` of `U(𝔟⁻)`. -/
abbrev monoLo (γ : LoIdx n →₀ ℕ) : UniversalEnvelopingAlgebra ℂ (bLo n) :=
  orderedMonomial ℂ (bLo n) (subBasis n _ (lo_trans n)) (loList n) γ

theorem subInc_monoUp (β : UpIdx n →₀ ℕ) :
    subInc n _ (up_trans n) (monoUp n β) = W n ((expand (upList n) β).map Subtype.val) :=
  subInc_word n _ (up_trans n) _

theorem subInc_monoLo (γ : LoIdx n →₀ ℕ) :
    subInc n _ (lo_trans n) (monoLo n γ) = W n ((expand (loList n) γ).map Subtype.val) :=
  subInc_word n _ (lo_trans n) _

/-- `E^α = E^{α⁺} E^{α⁻}` with both factors in the images of `U(𝔫⁺)` and `U(𝔟⁻)`. -/
theorem basisU_eq_subInc (α : Idx n →₀ ℕ) :
    basisU n α = subInc n _ (up_trans n) (monoUp n (α.subtypeDomain fun c => c.1 < c.2)) *
      subInc n _ (lo_trans n) (monoLo n (α.subtypeDomain fun c => ¬ c.1 < c.2)) := by
  rw [basisU_apply_split, subInc_monoUp, subInc_monoLo,
    expand_map _ _ _ _ (fun c _ => Finsupp.subtypeDomain_apply.symm),
    expand_map _ _ _ _ (fun c _ => Finsupp.subtypeDomain_apply.symm)]

/-- Conversely a product of ordered monomials of `U(𝔫⁺)` and `U(𝔟⁻)` is an ordered monomial. -/
theorem exists_basisU_eq (β : UpIdx n →₀ ℕ) (γ : LoIdx n →₀ ℕ) :
    ∃ α : Idx n →₀ ℕ, expand ((upList n).map Subtype.val) α =
        (expand (upList n) β).map Subtype.val ∧
      expand ((loList n).map Subtype.val) α = (expand (loList n) γ).map Subtype.val := by
  classical
  refine ⟨Finsupp.equivFunOnFinite.symm
    (fun c => if h : c.1 < c.2 then β ⟨c, h⟩ else γ ⟨c, h⟩), ?_, ?_⟩
  · refine expand_map _ _ _ _ fun c _ => ?_
    rw [Finsupp.coe_equivFunOnFinite_symm, dite_eq_left c.2]
  · refine expand_map _ _ _ _ fun c _ => ?_
    rw [Finsupp.coe_equivFunOnFinite_symm, dite_eq_right c.2]

/-! ## The functional `Ψ_v` -/

section Psi

variable (v : Idx n → ℂ)

/-- The value `∏ v(c)` over the letters of `E^α`. -/
def wt (α : Idx n →₀ ℕ) : ℂ := ((expand (bsList n) α).map v).prod

/-- The linear functional on `U(𝔤𝔩_n(ℂ))` with `Ψ_v(E^α) = ∏ v(c)` over the letters of `E^α`. -/
def Psi : VermaGL.glU n →ₗ[ℂ] ℂ := (basisU n).constr ℂ (wt n v)

theorem Psi_basisU (α : Idx n →₀ ℕ) : Psi n v (basisU n α) = wt n v α :=
  (basisU n).constr_basis ℂ _ α

theorem Psi_one : Psi n v 1 = 1 := by
  have h : basisU n 0 = 1 := by rw [basisU_apply, expand_zero]; rfl
  rw [← h, Psi_basisU, wt, expand_zero]
  rfl

variable (μU : nUp n →ₗ⁅ℂ⁆ ℂ) (μL : bLo n →ₗ⁅ℂ⁆ ℂ)
  (hU : ∀ c, μU (subBasis n _ (up_trans n) c) = v c.1)
  (hL : ∀ c, μL (subBasis n _ (lo_trans n) c) = v c.1)

include hU hL in
theorem Psi_monoUp_mul_monoLo (β : UpIdx n →₀ ℕ) (γ : LoIdx n →₀ ℕ) :
    Psi n v (subInc n _ (up_trans n) (monoUp n β) * subInc n _ (lo_trans n) (monoLo n γ)) =
      subChar n _ (up_trans n) μU (monoUp n β) * subChar n _ (lo_trans n) μL (monoLo n γ) := by
  obtain ⟨α, hα₁, hα₂⟩ := exists_basisU_eq n β γ
  rw [subInc_monoUp, subInc_monoLo, ← hα₁, ← hα₂, ← basisU_apply_split, Psi_basisU, wt,
    bsList, expand_append, List.map_append, List.prod_append, hα₁, hα₂]
  congr 1
  · rw [monoUp, orderedMonomial, subChar_word, List.map_map]
    congr 1
    exact List.map_congr_left fun c _ => (hU c).symm
  · rw [monoLo, orderedMonomial, subChar_word, List.map_map]
    congr 1
    exact List.map_congr_left fun c _ => (hL c).symm

theorem span_monoUp : Submodule.span ℂ (Set.range (monoUp n)) = ⊤ :=
  eq_top_iff.mpr (top_le_span_subMonomial n _ (up_trans n) (upList n) (upList_nodup n)
    (mem_upList n))

theorem span_monoLo : Submodule.span ℂ (Set.range (monoLo n)) = ⊤ :=
  eq_top_iff.mpr (top_le_span_subMonomial n _ (lo_trans n) (loList n) (loList_nodup n)
    (mem_loList n))

include hU hL in
/-- `Ψ_v(u u') = χ_U(u) χ_L(u')` for `u ∈ U(𝔫⁺)`, `u' ∈ U(𝔟⁻)`. -/
theorem Psi_subInc_mul (u : UniversalEnvelopingAlgebra ℂ (nUp n))
    (u' : UniversalEnvelopingAlgebra ℂ (bLo n)) :
    Psi n v (subInc n _ (up_trans n) u * subInc n _ (lo_trans n) u') =
      subChar n _ (up_trans n) μU u * subChar n _ (lo_trans n) μL u' := by
  have h1 : ∀ β : UpIdx n →₀ ℕ, ∀ u' : UniversalEnvelopingAlgebra ℂ (bLo n),
      Psi n v (subInc n _ (up_trans n) (monoUp n β) * subInc n _ (lo_trans n) u') =
        subChar n _ (up_trans n) μU (monoUp n β) * subChar n _ (lo_trans n) μL u' := by
    intro β
    have := LinearMap.ext_on_range (span_monoLo n)
      (f := Psi n v ∘ₗ LinearMap.mulLeft ℂ (subInc n _ (up_trans n) (monoUp n β)) ∘ₗ
        (subInc n _ (lo_trans n)).toLinearMap)
      (g := subChar n _ (up_trans n) μU (monoUp n β) • (subChar n _ (lo_trans n) μL).toLinearMap)
      (fun γ => by
        simpa using Psi_monoUp_mul_monoLo n v μU μL hU hL β γ)
    exact fun u' => by simpa using LinearMap.congr_fun this u'
  have := LinearMap.ext_on_range (span_monoUp n)
    (f := Psi n v ∘ₗ LinearMap.mulRight ℂ (subInc n _ (lo_trans n) u') ∘ₗ
      (subInc n _ (up_trans n)).toLinearMap)
    (g := subChar n _ (lo_trans n) μL u' • (subChar n _ (up_trans n) μU).toLinearMap)
    (fun β => by
      simpa [mul_comm] using h1 β u')
  simpa [mul_comm] using LinearMap.congr_fun this u

include hU hL in
/-- Right `𝔟⁻`-equivariance: `Ψ_v(u X) = μ_L(X) Ψ_v(u)`. -/
theorem Psi_mul_ι (u : VermaGL.glU n) (X : bLo n) :
    Psi n v (u * UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ)) =
      μL X * Psi n v u := by
  have := (basisU n).ext (f₁ := Psi n v ∘ₗ LinearMap.mulRight ℂ
      (UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ)))
    (f₂ := μL X • Psi n v) (fun α => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [basisU_eq_subInc, mul_assoc, ← subInc_ι n _ (lo_trans n) X, ← map_mul,
        Psi_subInc_mul n v μU μL hU hL, Psi_subInc_mul n v μU μL hU hL, map_mul, subChar_ι]
      ring)
  simpa using LinearMap.congr_fun this u

include hU hL in
/-- Left `𝔫⁺`-equivariance: `Ψ_v(X u) = μ_U(X) Ψ_v(u)`. -/
theorem Psi_ι_mul (u : VermaGL.glU n) (X : nUp n) :
    Psi n v (UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ) * u) =
      μU X * Psi n v u := by
  have := (basisU n).ext (f₁ := Psi n v ∘ₗ LinearMap.mulLeft ℂ
      (UniversalEnvelopingAlgebra.ι ℂ (X : Matrix (Fin n) (Fin n) ℂ)))
    (f₂ := μU X • Psi n v) (fun α => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [basisU_eq_subInc, ← mul_assoc, ← subInc_ι n _ (up_trans n) X, ← map_mul,
        Psi_subInc_mul n v μU μL hU hL, Psi_subInc_mul n v μU μL hU hL, map_mul, subChar_ι]
      ring)
  simpa using LinearMap.congr_fun this u

end Psi

/-! ## Characters of the triangular subalgebras -/

section Chars

/-- The character `X ↦ Σ_p λ_p X_pp` of `𝔟⁻`. -/
def muLo (lam : Fin n → ℂ) : bLo n →ₗ⁅ℂ⁆ ℂ where
  toFun X := ∑ p, lam p * (X : Matrix (Fin n) (Fin n) ℂ) p p
  map_add' X Y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a X := by
    rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    change lam p * (a • (X : Matrix (Fin n) (Fin n) ℂ)) p p = _
    rw [Matrix.smul_apply, smul_eq_mul]
    ring
  map_lie' := by
    intro X Y
    have hd : ∀ p, ((X : Matrix (Fin n) (Fin n) ℂ) * Y) p p =
        ((Y : Matrix (Fin n) (Fin n) ℂ) * X) p p := by
      intro p
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single p, Finset.sum_eq_single p]
      · ring
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [X.2 k p (not_not.mpr h), mul_zero]
        · rw [Y.2 p k (not_not.mpr h), zero_mul]
      · simp
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [Y.2 k p (not_not.mpr h), mul_zero]
        · rw [X.2 p k (not_not.mpr h), zero_mul]
      · simp
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, Matrix.sub_apply, hd, sub_self,
      mul_zero, Finset.sum_const_zero]
    rw [mul_comm, sub_self]

theorem muLo_apply (lam : Fin n → ℂ) (X : bLo n) :
    muLo n lam X = ∑ p, lam p * (X : Matrix (Fin n) (Fin n) ℂ) p p := rfl

/-- The coefficient of the superdiagonal character at the position `(p, q)`. -/
def supCoeff (a : Fin n → ℂ) (p q : Fin n) : ℂ := if (q : ℕ) = (p : ℕ) + 1 then a p else 0

/-- The superdiagonal character `X ↦ Σ_p a_p X_{p,p+1}` of `𝔫⁺`. -/
def muUp (a : Fin n → ℂ) : nUp n →ₗ⁅ℂ⁆ ℂ where
  toFun X := ∑ p, ∑ q, supCoeff n a p q * (X : Matrix (Fin n) (Fin n) ℂ) p q
  map_add' X Y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    change supCoeff n a p q * (c • (X : Matrix (Fin n) (Fin n) ℂ)) p q = _
    rw [Matrix.smul_apply, smul_eq_mul]
    ring
  map_lie' := by
    intro X Y
    have hz : ∀ p q : Fin n, (q : ℕ) = (p : ℕ) + 1 →
        (⁅(X : Matrix (Fin n) (Fin n) ℂ), (Y : Matrix (Fin n) (Fin n) ℂ)⁆) p q = 0 := by
      intro p q hpq
      rw [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
      have hk : ∀ k, (X : Matrix (Fin n) (Fin n) ℂ) p k * (Y : Matrix (Fin n) (Fin n) ℂ) k q = 0 ∧
          (Y : Matrix (Fin n) (Fin n) ℂ) p k * (X : Matrix (Fin n) (Fin n) ℂ) k q = 0 := by
        intro k
        by_cases h1 : p < k
        · have h2 : ¬ k < q := by
            intro h2
            have := Fin.lt_def.mp h1
            have := Fin.lt_def.mp h2
            omega
          exact ⟨by rw [Y.2 k q h2, mul_zero], by rw [X.2 k q h2, mul_zero]⟩
        · exact ⟨by rw [X.2 p k h1, zero_mul], by rw [Y.2 p k h1, zero_mul]⟩
      simp [hk]
    have hL : ∑ p : Fin n, ∑ q : Fin n, supCoeff n a p q *
        ((⁅X, Y⁆ : nUp n) : Matrix (Fin n) (Fin n) ℂ) p q = 0 := by
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
      rw [LieSubalgebra.coe_bracket]
      by_cases h : (q : ℕ) = (p : ℕ) + 1
      · rw [hz p q h, mul_zero]
      · rw [supCoeff, ite_eq_right h, zero_mul]
    change ∑ p : Fin n, ∑ q : Fin n, supCoeff n a p q *
        ((⁅X, Y⁆ : nUp n) : Matrix (Fin n) (Fin n) ℂ) p q = ⁅_, _⁆
    rw [hL, Ring.lie_def, mul_comm, sub_self]

/-- The values of the functional `Ψ` attached to `λ` and `a`: `a_p` on `E_{p,p+1}`, `λ_p` on
`E_pp`, and `0` on the other matrix units. -/
def vVal (lam a : Fin n → ℂ) (c : Idx n) : ℂ :=
  if c.1 < c.2 then supCoeff n a c.1 c.2 else if c.1 = c.2 then lam c.1 else 0

theorem muUp_subBasis (a : Fin n → ℂ) (lam : Fin n → ℂ) (c : UpIdx n) :
    muUp n a (subBasis n _ (up_trans n) c) = vVal n lam a c.1 := by
  change ∑ p, ∑ q, supCoeff n a p q *
    ((subBasis n _ (up_trans n) c : nUp n) : Matrix (Fin n) (Fin n) ℂ) p q = _
  rw [coe_subBasis, vVal, ite_eq_left c.2]
  simp only [unitE, Matrix.single_apply]
  rw [Finset.sum_eq_single c.1.1, Finset.sum_eq_single c.1.2]
  · simp
  · intro q _ hq
    rw [ite_eq_right (fun h => hq h.2.symm), mul_zero]
  · simp
  · intro p _ hp
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [ite_eq_right (fun h => hp h.1.symm), mul_zero]
  · simp

theorem muLo_subBasis (a : Fin n → ℂ) (lam : Fin n → ℂ) (c : LoIdx n) :
    muLo n lam (subBasis n _ (lo_trans n) c) = vVal n lam a c.1 := by
  rw [muLo_apply, coe_subBasis, vVal, ite_eq_right c.2]
  simp only [unitE, Matrix.single_apply]
  by_cases h : c.1.1 = c.1.2
  · rw [ite_eq_left h, Finset.sum_eq_single c.1.1]
    · simp [h]
    · intro p _ hp
      rw [ite_eq_right (fun h' => hp h'.1.symm), mul_zero]
    · simp
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ite_eq_right (fun h' => h (h'.1.trans h'.2.symm)), mul_zero]

end Chars

/-! ## The lower Verma module -/

section Verma

variable (lam : Fin n → ℂ)

theorem Psi_mul_unitE_lo (a : Fin n → ℂ) (c : LoIdx n) (u : VermaGL.glU n) :
    Psi n (vVal n lam a) (u * UniversalEnvelopingAlgebra.ι ℂ (unitE n c.1)) =
      vVal n lam a c.1 * Psi n (vVal n lam a) u := by
  have h := Psi_mul_ι n (vVal n lam a) (muUp n a) (muLo n lam) (muUp_subBasis n a lam)
    (muLo_subBasis n a lam) u (subBasis n _ (lo_trans n) c)
  rwa [coe_subBasis, muLo_subBasis n a lam] at h

theorem Psi_unitE_up_mul (a : Fin n → ℂ) (c : UpIdx n) (u : VermaGL.glU n) :
    Psi n (vVal n lam a) (UniversalEnvelopingAlgebra.ι ℂ (unitE n c.1) * u) =
      vVal n lam a c.1 * Psi n (vVal n lam a) u := by
  have h := Psi_ι_mul n (vVal n lam a) (muUp n a) (muLo n lam) (muUp_subBasis n a lam)
    (muLo_subBasis n a lam) u (subBasis n _ (up_trans n) c)
  rwa [coe_subBasis, muUp_subBasis n a lam] at h

theorem vVal_of_lt (a : Fin n → ℂ) {p q : Fin n} (h : q < p) : vVal n lam a (p, q) = 0 := by
  rw [vVal, ite_eq_right (not_lt.mpr h.le), ite_eq_right (ne_of_gt h)]

theorem vVal_diag (a : Fin n → ℂ) (p : Fin n) : vVal n lam a (p, p) = lam p := by
  rw [vVal, ite_eq_right (lt_irrefl p), ite_eq_left rfl]

/-- `Ψ_{λ,a}` vanishes on `U · x` for every `x` in the defining left ideal of `M⁻(λ)`. -/
theorem Psi_mul_mem_lowerVermaIdeal (a : Fin n → ℂ) {x : VermaGL.glU n}
    (hx : x ∈ VermaGL.lowerVermaIdeal n lam) (u : VermaGL.glU n) :
    Psi n (vVal n lam a) (u * x) = 0 := by
  induction hx using Submodule.span_induction generalizing u with
  | mem x hx =>
    rcases hx with ⟨p, q, hqp, rfl⟩ | ⟨p, rfl⟩
    · have h := Psi_mul_unitE_lo n lam a ⟨(p, q), not_lt.mpr hqp.le⟩ u
      rw [vVal_of_lt n lam a hqp, zero_mul] at h
      exact h
    · have h := Psi_mul_unitE_lo n lam a ⟨(p, p), lt_irrefl p⟩ u
      rw [vVal_diag] at h
      rw [mul_sub, map_sub, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact sub_eq_zero.mpr h
  | zero => rw [mul_zero, map_zero]
  | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, ← mul_assoc]; exact hx _

/-- **The generator of `M⁻(λ)` is nonzero.** -/
theorem gen_ne_zero : VermaGL.gen n lam ≠ 0 := by
  intro h
  have h1 : (1 : VermaGL.glU n) ∈ VermaGL.lowerVermaIdeal n lam :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  have h2 := Psi_mul_mem_lowerVermaIdeal n lam 0 h1 1
  rw [one_mul, Psi_one] at h2
  exact one_ne_zero h2

theorem mk_eq_smul_gen (u : VermaGL.glU n) :
    (Submodule.Quotient.mk u : VermaGL.LowerVerma n lam) = u • VermaGL.gen n lam :=
  (BGChase.smul_gen lam u).symm

theorem unitE_lo_smul_gen (a : Fin n → ℂ) (c : LoIdx n) :
    UniversalEnvelopingAlgebra.ι ℂ (unitE n c.1) • VermaGL.gen n lam =
      vVal n lam a c.1 • VermaGL.gen n lam := by
  have hmem : UniversalEnvelopingAlgebra.ι ℂ (unitE n c.1) -
      algebraMap ℂ (VermaGL.glU n) (vVal n lam a c.1) ∈ VermaGL.lowerVermaIdeal n lam := by
    obtain ⟨⟨p, q⟩, hc⟩ := c
    rcases lt_or_eq_of_le (not_lt.mp hc) with h | h
    · rw [vVal_of_lt n lam a h, map_zero, sub_zero]
      exact Submodule.subset_span (Or.inl ⟨p, q, h, rfl⟩)
    · dsimp only at h
      subst h
      rw [vVal_diag]
      exact Submodule.subset_span (Or.inr ⟨q, rfl⟩)
  have h0 := (Submodule.Quotient.mk_eq_zero (VermaGL.lowerVermaIdeal n lam)).mpr hmem
  rw [Submodule.Quotient.mk_sub, mk_eq_smul_gen, mk_eq_smul_gen, sub_eq_zero] at h0
  rw [h0, algebraMap_smul]

theorem W_lo_smul_gen (a : Fin n → ℂ) (l : List (Idx n)) (hl : ∀ c ∈ l, ¬ c.1 < c.2) :
    W n l • VermaGL.gen n lam = (l.map (vVal n lam a)).prod • VermaGL.gen n lam := by
  induction l with
  | nil => rw [W_nil, one_smul, List.map_nil, List.prod_nil, one_smul]
  | cons c l ih =>
    rw [W_cons, mul_smul, ih fun d hd => hl d (List.mem_cons_of_mem c hd), smul_comm,
      unitE_lo_smul_gen n lam a ⟨c, hl c List.mem_cons_self⟩, smul_smul, List.map_cons,
      List.prod_cons, mul_comm]

/-- `E^α · gen = (∏ λ) · E^{α⁺} · gen`. -/
theorem basisU_smul_gen (α : Idx n →₀ ℕ) :
    basisU n α • VermaGL.gen n lam =
      ((expand ((loList n).map Subtype.val) α).map (vVal n lam 0)).prod •
        (W n (expand ((upList n).map Subtype.val) α) • VermaGL.gen n lam) := by
  rw [basisU_apply_split, mul_smul, W_lo_smul_gen n lam 0, smul_comm]
  intro c hc
  obtain ⟨c', -, rfl⟩ := List.mem_map.mp (mem_expand hc)
  exact c'.2

theorem lie_diagonal_unitE (d : Fin n → ℂ) (c : Idx n) :
    ⁅Matrix.diagonal d, unitE n c⁆ = (d c.1 - d c.2) • unitE n c := by
  rw [Ring.lie_def]
  ext i j
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, unitE,
    Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [smul_eq_mul]
    ring
  · simp

theorem ι_diagonal_mul (d : Fin n → ℂ) (c : Idx n) :
    UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal d) * UniversalEnvelopingAlgebra.ι ℂ (unitE n c) =
      UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal d) +
        (d c.1 - d c.2) • UniversalEnvelopingAlgebra.ι ℂ (unitE n c) := by
  have h := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℂ) (Matrix.diagonal d) (unitE n c)
  rw [lie_diagonal_unitE, map_smul, Ring.lie_def] at h
  rw [h]
  abel

theorem diagonal_eq_sum (d : Fin n → ℂ) :
    Matrix.diagonal d = ∑ p, d p • unitE n (p, p) := by
  ext i j
  rw [Matrix.sum_apply, Finset.sum_eq_single i]
  · simp only [Matrix.smul_apply, unitE, Matrix.single_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.diagonal_apply_ne _ h]
      simp [h]
  · intro p _ hp
    simp [unitE, hp]
  · simp

theorem ι_diagonal_smul (d : Fin n → ℂ) (m : VermaGL.LowerVerma n lam)
    (hm : ∀ p, VermaGL.unitU n p p • m = lam p • m) :
    UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal d) • m = (∑ p, d p * lam p) • m := by
  rw [diagonal_eq_sum, map_sum, Finset.sum_smul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_assoc, ← smul_smul]
  congr 1
  exact hm p

theorem unitU_smul_gen (p : Fin n) :
    VermaGL.unitU n p p • VermaGL.gen n lam = lam p • VermaGL.gen n lam :=
  BGChase.unitU_smul_gen_diag lam p

/-- The vectors `w · gen` are weight vectors. -/
theorem W_eigen (d : Fin n → ℂ) (l : List (Idx n)) :
    UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal d) • (W n l • VermaGL.gen n lam) =
      ((∑ p, d p * lam p) + (l.map fun c => d c.1 - d c.2).sum) •
        (W n l • VermaGL.gen n lam) := by
  induction l with
  | nil =>
    rw [W_nil, one_smul, List.map_nil, List.sum_nil, add_zero]
    exact ι_diagonal_smul n lam d _ (unitU_smul_gen n lam)
  | cons c l ih =>
    rw [W_cons, mul_smul, smul_smul, ι_diagonal_mul, add_smul, mul_smul, ih, smul_comm,
      smul_assoc, ← add_smul, List.map_cons, List.sum_cons]
    congr 1
    ring

end Verma

end GLn

/-! ## The weight statement -/

/-- The diagonal entries `0, -1, -2, …` of the element `H₀` separating the weights. -/
def dZero (n : ℕ) : Fin n → ℂ := fun p => -((p : ℕ) : ℂ)

theorem sum_shift_ne_zero (n : ℕ) (l : List (Idx n)) (hl : ∀ c ∈ l, c.1 < c.2) (hne : l ≠ []) :
    (l.map fun c => dZero n c.1 - dZero n c.2).sum ≠ 0 := by
  have h : (l.map fun c => dZero n c.1 - dZero n c.2) =
      (l.map fun c => (((c.2 : ℕ) - (c.1 : ℕ) : ℕ) : ℂ)) := by
    refine List.map_congr_left fun c hc => ?_
    rw [dZero, dZero, Nat.cast_sub (Fin.lt_def.mp (hl c hc)).le]
    ring
  have h' : (l.map fun c => (((c.2 : ℕ) - (c.1 : ℕ) : ℕ) : ℂ)).sum =
      (((l.map fun c => (c.2 : ℕ) - (c.1 : ℕ)).sum : ℕ) : ℂ) := by
    rw [Nat.cast_list_sum, List.map_map]
    rfl
  rw [h, h', Nat.cast_ne_zero]
  have h1 : ∀ i ∈ l.map (fun c => (c.2 : ℕ) - (c.1 : ℕ)), 1 ≤ i := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hi
    have := Fin.lt_def.mp (hl c hc)
    omega
  have h2 := List.length_le_sum_of_one_le _ h1
  rw [List.length_map] at h2
  have h3 : 0 < l.length := List.length_pos_iff.mpr hne
  omega

/-- **The lower Verma weight statement.** `gen n λ ≠ 0`, and every vector of weight `λ` in
`M⁻(λ)` is a multiple of `gen n λ`. -/
theorem lowerVermaWeight : VermaGL.LowerVermaWeightStatement := by
  intro n lam
  refine ⟨gen_ne_zero n lam, fun m hm => ?_⟩
  set T : Module.End ℂ (VermaGL.LowerVerma n lam) :=
    VermaGL.action n lam (Matrix.diagonal (dZero n)) with hT
  have hTx : ∀ x, T x = UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal (dZero n)) • x :=
    fun x => rfl
  set μ₀ : ℂ := ∑ p, dZero n p * lam p with hμ₀
  have hgen : T (VermaGL.gen n lam) = μ₀ • VermaGL.gen n lam := by
    rw [hTx]
    exact ι_diagonal_smul n lam _ _ (unitU_smul_gen n lam)
  have hTm : T m = μ₀ • m := by
    rw [hTx]
    exact ι_diagonal_smul n lam _ m hm
  set N : Submodule ℂ (VermaGL.LowerVerma n lam) :=
    ⨆ (μ : ℂ) (_ : μ ≠ μ₀), Module.End.eigenspace T μ with hN
  have hall : ∀ x : VermaGL.LowerVerma n lam, x ∈ (ℂ ∙ VermaGL.gen n lam) ⊔ N := by
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
      set l := expand ((upList n).map Subtype.val) α
      have hl : ∀ c ∈ l, c.1 < c.2 := by
        intro c hc
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp (mem_expand hc)
        exact c'.2
      by_cases hne : l = []
      · rw [hne, W_nil, one_smul]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hk := sum_shift_ne_zero n l hl hne
        have hmem : W n l • VermaGL.gen n lam ∈ Module.End.eigenspace T
            (μ₀ + (l.map fun c => dZero n c.1 - dZero n c.2).sum) := by
          rw [Module.End.mem_eigenspace_iff, hTx]
          exact W_eigen n lam (dZero n) l
        refine (le_iSup₂ (f := fun (μ : ℂ) (_ : μ ≠ μ₀) => Module.End.eigenspace T μ) _
          ?_) hmem
        intro h
        apply hk
        linear_combination h
    | zero => rw [Submodule.Quotient.mk_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ r hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hall m)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hTz : T z = μ₀ • z := by
    have hz' : z = m - c • VermaGL.gen n lam := by rw [← hyz]; abel
    rw [hz', map_sub, map_smul, hTm, hgen, smul_sub, smul_comm]
  have hz0 : z = 0 := by
    have hdisj := (iSupIndep_def.mp (Module.End.eigenspaces_iSupIndep T)) μ₀
    exact (Submodule.disjoint_def.mp hdisj) z (Module.End.mem_eigenspace_iff.mpr hTz) hz
  exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

end Langlands.Archimedean.VermaPBW
