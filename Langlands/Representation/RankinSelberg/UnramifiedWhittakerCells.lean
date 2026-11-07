import Langlands.Representation.Unramified.MinusculeCosets
import Langlands.Representation.Whittaker.Spherical
import Langlands.Representation.Whittaker.UpperUnipotentCharacterFactorization

/-!
# Torus values of spherical Whittaker functions

For a field with a valuation, a uniformizing element `ϖ`, the integral group
`K = GL_(n+1)(O)` and a character `θ` of the upper unipotent group that is trivial on
its integral points, let `f` be a `θ`-equivariant, right `K`-invariant function on
`GL_(n+1)`. This module evaluates `f` at the products of a dominant torus element
`ϖ ^ lam` with the labelled minuscule coset representatives, and proves that `f`
vanishes at `ϖ ^ lam` for non-dominant `lam` when `θ` is nontrivial on
`1 + ϖ⁻¹ O E_(i,i+1)` for every `i`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedWhittaker

open Matrix Langlands.Conductor Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa
open Langlands.Unramified.MinusculeCosets
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit transvection_apply)

universe uF uΓ uΛ

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀}

/-! ### Torus arithmetic -/

theorem torus_mul_torus {m : ℕ} (ϖ : Fˣ) (lam mu : Fin m → ℤ) :
    torus ϖ lam * torus ϖ mu = torus ϖ (lam + mu) := by
  rw [torus, torus, torus, ← map_mul]
  congr 1
  funext i
  simp [zpow_add]

theorem torus_conj_apply {m : ℕ} (ϖ : Fˣ) (lam : Fin m → ℤ)
    (g : Matrix.GeneralLinearGroup (Fin m) F) (a b : Fin m) :
    (torus ϖ lam * g * (torus ϖ lam)⁻¹) a b =
      ((ϖ ^ lam a : Fˣ) : F) * g a b * (((ϖ ^ lam b)⁻¹ : Fˣ) : F) := by
  rw [torus_inv, torus, diagonalUnits_mul_mul_apply]

/-- Conjugation by a torus element preserves the upper unipotent group. -/
theorem torus_conj_mem_upperUnipotent {m : ℕ} (ϖ : Fˣ) (lam : Fin m → ℤ)
    {g : Matrix.GeneralLinearGroup (Fin m) F} (hg : g ∈ upperUnipotent m F) :
    torus ϖ lam * g * (torus ϖ lam)⁻¹ ∈ upperUnipotent m F := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · have hba' : b < a := hba
    change (torus ϖ lam * g * (torus ϖ lam)⁻¹) a b = 0
    rw [torus_conj_apply, show g a b = 0 from hg.1 hba', mul_zero, zero_mul]
  · change (torus ϖ lam * g * (torus ϖ lam)⁻¹) a a = 1
    rw [torus_conj_apply, show g a a = 1 from hg.2 a, mul_one, Units.mul_inv]

/-! ### Integrality of conjugated radical elements -/

theorem radicalElement_entry_mem {m : ℕ} (S : Finset (Fin m))
    {c : Fin m → Fin m → F} (hc : ∀ a b, IsRadicalPair S a b → c a b ∈ v.integer)
    (a b : Fin m) : radicalElement S c a b ∈ v.integer := by
  rw [radicalElement_apply]
  refine add_mem ?_ ?_
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · split_ifs with h
    · exact hc a b h
    · exact zero_mem _

/-- For dominant `lam`, conjugating an integral radical element by `ϖ ^ lam` gives an
integral matrix. -/
theorem torus_conj_radicalElement_mem {n : ℕ} {ϖ : Fˣ} (hϖ : v (ϖ : F) ≤ 1)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) (S : Finset (Fin (n + 1)))
    {c : Fin (n + 1) → Fin (n + 1) → F}
    (hc : ∀ a b, IsRadicalPair S a b → c a b ∈ v.integer) :
    torus ϖ lam * radicalElement S c * (torus ϖ lam)⁻¹ ∈ integralSubgroup v.integer n := by
  have hu := radicalElement_mem_upperUnipotent S c
  have hu' := radicalElement_mem_upperUnipotent S (-c)
  have hc' : ∀ a b, IsRadicalPair S a b → (-c) a b ∈ v.integer := fun a b h =>
    neg_mem (hc a b h)
  refine (mem_integralSubgroup v.integer n _).2 ⟨?_, ?_⟩
  · exact torus_conj_entry_mem hϖ hlam (torus_conj_mem_upperUnipotent ϖ lam hu).1
      (radicalElement_entry_mem S hc) rfl
  · have hinv : (torus ϖ lam * radicalElement S c * (torus ϖ lam)⁻¹)⁻¹ =
        torus ϖ lam * radicalElement S (-c) * (torus ϖ lam)⁻¹ := by
      rw [← radicalElement_inv]
      group
    rw [hinv]
    exact torus_conj_entry_mem hϖ hlam (torus_conj_mem_upperUnipotent ϖ lam hu').1
      (radicalElement_entry_mem S hc') rfl

/-! ### Values at dominant translates of coset representatives -/

section Values

variable {n : ℕ} {θ : upperUnipotent (n + 1) F →* ℂˣ}

/-- A `θ`-equivariant function is unchanged by left multiplication with a unipotent
element that is integral, when `θ` is integrally trivial. -/
theorem eval_integral_unipotent_mul (hθ : IsIntegrallyTrivial v θ)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g, f (u.val * g) = (θ u : ℂ) * f g)
    {u : Matrix.GeneralLinearGroup (Fin (n + 1)) F} (hu : u ∈ upperUnipotent (n + 1) F)
    (huK : u ∈ integralSubgroup v.integer n) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    f (u * g) = f g := by
  have h := hf ⟨u, hu⟩ g
  rw [hθ ⟨u, hu⟩ huK, Units.val_one, one_mul] at h
  exact h

/-- The value at `ϖ ^ lam` times a coset representative of a minuscule double coset is the
value at `ϖ ^ (lam + 1_S)`, for dominant `lam` and integral radical entries. -/
theorem eval_torus_mul_cosetRep {ϖ : Fˣ} (hϖ : v (ϖ : F) ≤ 1) (hθ : IsIntegrallyTrivial v θ)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g, f (u.val * g) = (θ u : ℂ) * f g)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) (S : Finset (Fin (n + 1)))
    {c : Fin (n + 1) → Fin (n + 1) → F}
    (hc : ∀ a b, IsRadicalPair S a b → c a b ∈ v.integer) :
    f (torus ϖ lam * cosetRep ϖ S c) = f (torus ϖ (lam + subsetExponent S)) := by
  have heq : torus ϖ lam * cosetRep ϖ S c =
      (torus ϖ lam * radicalElement S c * (torus ϖ lam)⁻¹) *
        torus ϖ (lam + subsetExponent S) := by
    rw [cosetRep, subsetTorus, ← torus_mul_torus]
    group
  rw [heq]
  exact eval_integral_unipotent_mul hθ hf
    (torus_conj_mem_upperUnipotent ϖ lam (radicalElement_mem_upperUnipotent S c))
    (torus_conj_radicalElement_mem hϖ hlam S hc) _

variable {Λ : Type uΛ} {σ : Λ → F}

theorem eval_torus_mul_labelledRep {ϖ : Fˣ} (hϖ : v (ϖ : F) ≤ 1)
    (hθ : IsIntegrallyTrivial v θ)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g, f (u.val * g) = (θ u : ℂ) * f g)
    (hσ : ∀ x, σ x ∈ v.integer)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) {i : ℕ} (α : CosetIndex Λ (n + 1) i) :
    f (torus ϖ lam * labelledRep ϖ σ α) = f (torus ϖ (lam + subsetExponent α.1.1)) := by
  refine eval_torus_mul_cosetRep hϖ hθ hf hlam α.1.1 fun a b hab => ?_
  simp only [liftCoeff, hab, ↓reduceDIte]
  exact hσ _

/-- Summing over the labelled representatives counts each subset `S` with the number of
labellings of its radical pairs. -/
theorem sum_eval_torus_mul_labelledRep [Fintype Λ] {ϖ : Fˣ} (hϖ : v (ϖ : F) ≤ 1)
    (hθ : IsIntegrallyTrivial v θ)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g, f (u.val * g) = (θ u : ℂ) * f g)
    (hσ : ∀ x, σ x ∈ v.integer)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) (i : ℕ) :
    ∑ α : CosetIndex Λ (n + 1) i, f (torus ϖ lam * labelledRep ϖ σ α) =
      ∑ S : {S : Finset (Fin (n + 1)) // S.card = i},
        (Fintype.card Λ : ℂ) ^ Fintype.card (RadicalPairs S.1) *
          f (torus ϖ (lam + subsetExponent S.1)) := by
  classical
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp_rw [fun w : RadicalPairs S.1 → Λ =>
    eval_torus_mul_labelledRep (α := ⟨S, w⟩) hϖ hθ hf hσ hlam]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  push_cast
  ring

end Values

/-! ### Vanishing away from dominant exponents -/

section Vanishing

variable {n : ℕ} {θ : upperUnipotent (n + 1) F →* ℂˣ}

theorem adjacentUnit_mem_integralSubgroup (i : Fin n) {x : F} (hx : x ∈ v.integer) :
    (adjacentUnit i x : Matrix.GeneralLinearGroup (Fin (n + 1)) F) ∈
      integralSubgroup v.integer n := by
  refine (mem_integralSubgroup v.integer n _).2 ⟨fun a b => ?_, fun a b => ?_⟩
  · exact transvection_mem v _ _ hx a b
  · exact transvection_mem v _ _ (neg_mem hx) a b

/-- Conjugating `1 + x E_(i,i+1)` by `ϖ ^ lam` from the inverse side. -/
theorem torus_inv_conj_adjacentUnit {ϖ : Fˣ} (lam : Fin (n + 1) → ℤ) (i : Fin n) (x : F) :
    (torus ϖ lam)⁻¹ * (adjacentUnit i x : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
        torus ϖ lam =
      adjacentUnit i ((((ϖ ^ lam i.castSucc)⁻¹ : Fˣ) : F) * x * ((ϖ ^ lam i.succ : Fˣ) : F)) := by
  have h : (torus ϖ lam)⁻¹ = torus ϖ (-lam) := by
    rw [torus_inv, torus]
    congr 1
    funext j
    simp [zpow_neg]
  have h' : torus ϖ lam = (torus ϖ (-lam))⁻¹ := by
    rw [← h, inv_inv]
  rw [h, h']
  apply Units.ext
  ext a b
  change (torus ϖ (-lam) * _ * (torus ϖ (-lam))⁻¹) a b = Matrix.transvection _ _ _ a b
  rw [torus_conj_apply]
  change _ * Matrix.transvection i.castSucc i.succ x a b * _ = _
  rw [transvection_apply, transvection_apply]
  by_cases hab : a = b
  · subst hab
    have h2 : ¬ (i.castSucc = a ∧ i.succ = a) := fun h =>
      (ne_of_lt Fin.castSucc_lt_succ) (h.1.trans h.2.symm)
    simp only [h2, ite_true, ite_false, add_zero, mul_one]
    simp [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ ϖ.ne_zero)]
  · by_cases h2 : i.castSucc = a ∧ i.succ = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp [hab, zpow_neg]
    · simp [hab, h2]

/-- A `θ`-equivariant right `K`-invariant function vanishes at `ϖ ^ lam` for every
non-dominant `lam`, provided `θ` is nontrivial on `1 + ϖ⁻¹ O E_(i,i+1)` for every `i`. -/
theorem eval_torus_eq_zero_of_not_antitone {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g, f (u.val * g) = (θ u : ℂ) * f g)
    (hK : ∀ g, ∀ k ∈ integralSubgroup v.integer n, f (g * k) = f g)
    (hθ : ∀ i : Fin n, ∃ x : F, v x * v (ϖ : F) ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    {lam : Fin (n + 1) → ℤ} (hlam : ¬ Antitone lam) : f (torus ϖ lam) = 0 := by
  rw [Fin.antitone_iff_succ_le] at hlam
  push Not at hlam
  obtain ⟨i, hi⟩ := hlam
  obtain ⟨x, hxv, hxθ⟩ := hθ i
  set t := torus ϖ lam
  set y : F := (((ϖ ^ lam i.castSucc)⁻¹ : Fˣ) : F) * x * ((ϖ ^ lam i.succ : Fˣ) : F) with hy
  have hv0 : 0 < v (ϖ : F) := valuation_pos v ϖ
  have hyv : y ∈ v.integer := by
    rw [Valuation.mem_integer_iff, hy, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀,
      mul_comm (v (ϖ : F) ^ lam i.castSucc)⁻¹, mul_assoc, inv_mul_eq_div,
      ← zpow_sub₀ hv0.ne']
    have hd : 1 ≤ lam i.succ - lam i.castSucc := by omega
    calc v x * v (ϖ : F) ^ (lam i.succ - lam i.castSucc)
        ≤ v x * v (ϖ : F) ^ (1 : ℤ) := by
          exact mul_le_mul_right (zpow_le_zpow_right_of_le_one₀ hv0 hϖ.1.le hd) _
      _ = v x * v (ϖ : F) := by rw [zpow_one]
      _ ≤ 1 := hxv
  have hk : t⁻¹ * (adjacentUnit i x : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * t ∈
      integralSubgroup v.integer n := by
    rw [torus_inv_conj_adjacentUnit]
    exact adjacentUnit_mem_integralSubgroup i hyv
  have h1 : f ((adjacentUnit i x : upperUnipotent (n + 1) F).val * t) = f t := by
    have : (adjacentUnit i x : upperUnipotent (n + 1) F).val * t =
        t * (t⁻¹ * (adjacentUnit i x : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * t) := by
      group
    rw [this, hK _ _ hk]
  rw [hf] at h1
  have h2 : ((θ (adjacentUnit i x) : ℂ) - 1) * f t = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exfalso
    apply hxθ
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.1 h
  · exact h

end Vanishing

end Langlands.RankinSelberg.UnramifiedWhittaker
