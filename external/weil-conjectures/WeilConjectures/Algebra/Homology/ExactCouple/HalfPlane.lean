/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Convergence
public import WeilConjectures.Algebra.Homology.ExactCouple.EdgeCollapse

/-!
# Convergence of half-plane exact couples

We consider exact couples `X` indexed by `(p, n) ∈ ℤ × ℤ` (filtration degree `p`, total degree
`n`) with `α` of degree `(-1, 0)` and `g` of degree `0`, as in
`WeilConjectures/Algebra/Homology/ExactCouple/Convergence.lean`, and whose map `f` has a degree
`b` with `1 ≤ b.1` (for the couples of blueprint `def-sp-exact-couple`, `b = (2, 1)`). Writing
`q = n - p`, such a couple is a *half-plane couple* with bound `a` if `D^{p, n} = 0` for `q < a`
and `E^{p, n} = 0` unless `p ≥ 0` and `q ≥ a` (`CategoryTheory.ExactCouple.IsHalfPlane`).

For such a couple, the maps `α : D^{p + 1, n} ⟶ D^{p, n}` are isomorphisms for `p < 0`, and
the spectral sequence converges to `Aⁿ = D^{0, n}` with the filtration
`Fᵖ Aⁿ = im (αᵖ : D^{p, n} ⟶ D^{0, n})` for `p ≥ 0`, which is finite, exhaustive and separated:
`Fᵖ Aⁿ = Aⁿ` for `p ≤ 0` and `Fᵖ Aⁿ = 0` for `p > n - a`. The couple is regular and complete,
and the differentials of the `N`-th derived couple leaving and arriving at `(p, n)` vanish as
soon as `N + 2 > max (n - p - a + 1) p` (when `b = (2, 1)`, so that the `N`-th derived couple
is the page `E_{N + 2}`).

## Main definitions

- `CategoryTheory.ExactCouple.IsHalfPlane`: half-plane couples.
- `CategoryTheory.ExactCouple.halfPlaneFiltration`: the filtration of the abutment `D^{0, n}`.
- `CategoryTheory.ExactCouple.halfPlaneConvergenceData`: the convergence of the spectral sequence
  to this filtration.
- `CategoryTheory.ExactCouple.halfPlaneDerivedIterEIsoGr`: the stable entries, for `b = (2, 1)`.

## Main statements

- `CategoryTheory.ExactCouple.convergesTo_halfPlaneFiltration`: convergence.
- `CategoryTheory.ExactCouple.isFiniteSeparated_halfPlaneFiltration`: the filtration is finite
  and separated (and exhaustive: `halfPlaneFiltration_F_eq_top`).
- `CategoryTheory.ExactCouple.isRegular_of_isHalfPlane`,
  `CategoryTheory.ExactCouple.isComplete_of_isHalfPlane`: regularity and completeness.
- `CategoryTheory.ExactCouple.derivedIter_d_eq_zero_of_isHalfPlane`: the bound for the
  stabilisation of the entries.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

section αPow

variable {κ : Type w} [AddCommGroup κ] {a b c : κ} (X : ExactCouple C a b c)

/-- The composite `α⁰ : D k ⟶ D i` for `k = i`. -/
lemma αPow_zero (k i : κ) (h : k = i) : X.αPow 0 k i = eqToHom (congrArg X.D h) := by
  rw [αPow, dite_eq_left h]

/-- The composite `αᴺ⁺¹` is `αᴺ` followed by `α`. -/
lemma αPow_succ (N : ℕ) (k i : κ) : X.αPow (N + 1) k i = X.αPow N k (i - a) ≫ X.α (i - a) i :=
  rfl

/-- The composite `αᴺ⁺¹ : D k ⟶ D i` is `αᴺ : D k ⟶ D j` followed by `α : D j ⟶ D i`. -/
lemma αPow_succ_of_add_eq (N : ℕ) (k j i : κ) (h : j + a = i) :
    X.αPow (N + 1) k i = X.αPow N k j ≫ X.α j i := by
  obtain rfl : j = i - a := eq_sub_of_add_eq h
  rfl

/-- Precomposing `α` with an `eqToHom`. -/
@[reassoc]
lemma eqToHom_comp_α {i j : κ} (h : i = j) (k : κ) :
    eqToHom (congrArg X.D h) ≫ X.α j k = X.α i k := by
  subst h
  simp

/-- The composite `αᴺ⁺¹` is `α` followed by `αᴺ`. -/
lemma αPow_succ' (N : ℕ) (k j i : κ) (h : k + a = j) :
    X.αPow (N + 1) k i = X.α k j ≫ X.αPow N j i := by
  induction N generalizing i with
  | zero =>
    rw [αPow_succ]
    by_cases hi : j = i
    · subst hi
      rw [X.αPow_zero k (j - a) (eq_sub_of_add_eq h), X.αPow_zero j j rfl,
        eqToHom_comp_α _ (eq_sub_of_add_eq h),
        eqToHom_refl, Category.comp_id]
    · rw [αPow, dite_eq_right (fun h' ↦ hi (by rw [← h, h', sub_add_cancel])), αPow,
        dite_eq_right hi,
        zero_comp, comp_zero]
  | succ N ih =>
    rw [X.αPow_succ (N + 1) k i, ih (i - a), Category.assoc, ← X.αPow_succ N j i]

end αPow

section HalfPlane

variable {b : ℤ × ℤ} (X : ExactCouple C ((-1, 0) : ℤ × ℤ) b 0)

/-- An exact couple indexed by `(p, n)` (filtration degree `p`, total degree `n`) is a
*half-plane couple* with bound `a` if, writing `q = n - p`, `D^{p, n} = 0` for `q < a` and
`E^{p, n} = 0` unless `p ≥ 0` and `q ≥ a`.

(blueprint: `thm-sp-half-plane-convergence`) -/
structure IsHalfPlane (a : ℤ) : Prop where
  isZero_D (p n : ℤ) (h : n - p < a) : IsZero (X.D (p, n))
  isZero_E (p n : ℤ) (h : p < 0 ∨ n - p < a) : IsZero (X.E (p, n))

variable {X} {a : ℤ} (h : X.IsHalfPlane a) (hb : 1 ≤ b.1)

include h hb in
/-- In a half-plane couple, `α : D^{p + 1, n} ⟶ D^{p, n}` is an isomorphism for `p < 0`. -/
lemma IsHalfPlane.isIso_α (p n : ℤ) (hp : p < 0) : IsIso (X.α (p + 1, n) (p, n)) := by
  have hm : Mono (X.α (p + 1, n) (p, n)) :=
    (X.exact_f_α (p + 1 - b.1, n - b.2) (p + 1, n) (p, n) (by ext <;> simp)
      (by ext <;> simp)).mono_g
      ((h.isZero_E _ _ (Or.inl (by omega))).eq_of_src _ _)
  have he : Epi (X.α (p + 1, n) (p, n)) :=
    (X.exact_α_g (p + 1, n) (p, n) (p, n) (by ext <;> simp) (by simp)).epi_f
      ((h.isZero_E _ _ (Or.inl hp)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

include h hb in
/-- In a half-plane couple, `α⁻ᵖ : D^{0, n} ⟶ D^{p, n}` is an isomorphism for `p ≤ 0`. -/
lemma IsHalfPlane.isIso_αPow (n : ℤ) (N : ℕ) (p : ℤ) (hp : p + N = 0) :
    IsIso (X.αPow N (0, n) (p, n)) := by
  induction N generalizing p with
  | zero =>
    obtain rfl : p = 0 := by simpa using hp
    rw [X.αPow_zero _ _ rfl, eqToHom_refl]
    infer_instance
  | succ N ih =>
    have := ih (p + 1) (by push_cast at hp; omega)
    have := h.isIso_α hb p n (by omega)
    rw [X.αPow_succ_of_add_eq N _ (p + 1, n) (p, n) (by ext <;> simp)]
    infer_instance

/-- The maps `ι : D^{p, n} ⟶ Aⁿ = D^{0, n}` of a half-plane couple: the composite `αᵖ` for
`p ≥ 0`, and the inverse of the isomorphism `α⁻ᵖ : D^{0, n} ⟶ D^{p, n}` for `p < 0`. -/
noncomputable def halfPlaneι (p n : ℤ) : X.D (p, n) ⟶ X.D (0, n) :=
  if hp : 0 ≤ p then X.αPow p.toNat (p, n) (0, n)
  else
    have := h.isIso_αPow hb n (-p).toNat p (by omega)
    inv (X.αPow (-p).toNat (0, n) (p, n))

/-- The map `ι : D^{p, n} ⟶ D^{0, n}` is `αᵖ` for `p ≥ 0`. -/
lemma halfPlaneι_of_nonneg (p n : ℤ) (hp : 0 ≤ p) :
    halfPlaneι h hb p n = X.αPow p.toNat (p, n) (0, n) := by
  rw [halfPlaneι, dite_eq_left hp]

/-- The map `ι : D^{p, n} ⟶ D^{0, n}` is the inverse of `α⁻ᵖ` for `p < 0`. -/
lemma halfPlaneι_of_neg (p n : ℤ) (hp : p < 0) :
    halfPlaneι h hb p n =
      (have := h.isIso_αPow hb n (-p).toNat p (by omega)
      inv (X.αPow (-p).toNat (0, n) (p, n))) := by
  rw [halfPlaneι, dite_eq_right (by omega)]

/-- The map `ι : D^{p, n} ⟶ D^{0, n}` is an isomorphism for `p ≤ 0`. -/
lemma isIso_halfPlaneι (p n : ℤ) (hp : p ≤ 0) : IsIso (halfPlaneι h hb p n) := by
  by_cases hp' : p = 0
  · subst hp'
    rw [halfPlaneι_of_nonneg h hb 0 n le_rfl, Int.toNat_zero, X.αPow_zero _ _ rfl]
    infer_instance
  · rw [halfPlaneι_of_neg h hb p n (by omega)]
    infer_instance

/-- The maps `ι : D^{p, n} ⟶ D^{0, n}` are compatible with `α`. -/
lemma α_comp_halfPlaneι (p n : ℤ) :
    X.α (p + 1, n) (p, n) ≫ halfPlaneι h hb p n = halfPlaneι h hb (p + 1) n := by
  by_cases hp : 0 ≤ p
  · rw [halfPlaneι_of_nonneg h hb p n hp, halfPlaneι_of_nonneg h hb (p + 1) n (by omega),
      show (p + 1).toNat = p.toNat + 1 by omega,
      X.αPow_succ' p.toNat (p + 1, n) (p, n) (0, n) (by ext <;> simp)]
  · have := h.isIso_α hb p n (by omega)
    have hA := h.isIso_αPow hb n (-(p + 1)).toNat (p + 1) (by omega)
    have hB := h.isIso_αPow hb n (-p).toNat p (by omega)
    have e : X.αPow (-p).toNat (0, n) (p, n) =
        X.αPow (-(p + 1)).toNat (0, n) (p + 1, n) ≫ X.α (p + 1, n) (p, n) := by
      rw [show (-p).toNat = (-(p + 1)).toNat + 1 by omega]
      exact X.αPow_succ_of_add_eq _ _ _ _ (by ext <;> simp)
    rw [halfPlaneι_of_neg h hb p n (by omega)]
    simp only [e, IsIso.inv_comp, IsIso.hom_inv_id_assoc]
    by_cases hp' : p + 1 = 0
    · rw [halfPlaneι_of_nonneg h hb (p + 1) n (by omega)]
      refine IsIso.inv_eq_of_hom_inv_id ?_
      have h₁ : (-(p + 1)).toNat = 0 := by omega
      have h₂ : (p + 1).toNat = 0 := by omega
      rw [h₁, h₂, X.αPow_zero _ _ (by ext <;> simp [hp']), X.αPow_zero _ _ (by ext <;> simp [hp']),
        eqToHom_trans, eqToHom_refl]
    · rw [halfPlaneι_of_neg h hb (p + 1) n (by omega)]

/-- The filtration `Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)` of the abutment `Aⁿ = D^{0, n}` of a half-plane
couple: `Fᵖ Aⁿ = im (αᵖ : D^{p, n} ⟶ D^{0, n})` for `p ≥ 0` and `Fᵖ Aⁿ = Aⁿ` for `p ≤ 0`.

(blueprint: `thm-sp-half-plane-convergence`) -/
noncomputable def halfPlaneFiltration (n : ℤ) : DecreasingFiltration (X.D (0, n)) :=
  X.abutmentFiltration (halfPlaneι h hb) (α_comp_halfPlaneι h hb) n

/-- For `p ≥ 0`, `Fᵖ Aⁿ` is the image of `αᵖ : D^{p, n} ⟶ D^{0, n}`. -/
lemma halfPlaneFiltration_F_eq (n p : ℤ) (hp : 0 ≤ p) :
    (halfPlaneFiltration h hb n).F p = imageSubobject (X.αPow p.toNat (p, n) (0, n)) := by
  rw [← halfPlaneι_of_nonneg h hb p n hp]
  rfl

/-- The filtration of the abutment of a half-plane couple is exhaustive: `Fᵖ Aⁿ = Aⁿ` for
`p ≤ 0`. -/
lemma halfPlaneFiltration_F_eq_top (n p : ℤ) (hp : p ≤ 0) :
    (halfPlaneFiltration h hb n).F p = ⊤ := by
  have := isIso_halfPlaneι h hb p n hp
  change imageSubobject (halfPlaneι h hb p n) = ⊤
  rw [imageSubobject_mono, Subobject.mk_eq_top_of_isIso]

/-- The filtration of the abutment of a half-plane couple vanishes in degrees `p > n - a`. -/
lemma halfPlaneFiltration_F_eq_bot (n p : ℤ) (hp : n - a < p) :
    (halfPlaneFiltration h hb n).F p = ⊥ := by
  change imageSubobject (halfPlaneι h hb p n) = ⊥
  rw [(h.isZero_D p n (by omega)).eq_of_src (halfPlaneι h hb p n) 0, imageSubobject_zero]

/-- The filtration of the abutment of a half-plane couple is finite and separated.

(blueprint: `thm-sp-half-plane-convergence`) -/
lemma isFiniteSeparated_halfPlaneFiltration (n : ℤ) :
    (halfPlaneFiltration h hb n).IsFiniteSeparated := by
  refine ⟨halfPlaneFiltration_F_eq_top h hb n 0 le_rfl,
    ⟨n - a + 1, halfPlaneFiltration_F_eq_bot h hb n _ (by omega)⟩, fun P hP ↦ ?_⟩
  rw [← le_bot_iff, ← halfPlaneFiltration_F_eq_bot h hb n (n - a + 1) (by omega)]
  exact hP _

/-- **The convergence data of a half-plane couple.** The spectral sequence of a half-plane
couple converges to `Aⁿ = D^{0, n}` with the filtration `Fᵖ Aⁿ = im (αᵖ : D^{p, n} ⟶ D^{0, n})`:
`E_∞^{p, n} ≅ Fᵖ Aⁿ / Fᵖ⁺¹ Aⁿ`, compatibly with the maps `D^{p, n} ⟶ D^{0, n}`.

(blueprint: `thm-sp-half-plane-convergence`) -/
noncomputable def halfPlaneConvergenceData :
    X.ConvergenceData (halfPlaneι h hb) (halfPlaneFiltration h hb) :=
  X.abutmentConvergenceData (halfPlaneι h hb) (α_comp_halfPlaneι h hb)
    (fun n ↦ ⟨0, fun p hp ↦ isIso_halfPlaneι h hb p n hp⟩)
    (fun n ↦ ⟨n - a + 1, fun p hp ↦ h.isZero_D p n (by omega)⟩)

/-- **Convergence of a half-plane couple.** The spectral sequence of a half-plane couple
converges to `Aⁿ = D^{0, n}` with the filtration `Fᵖ Aⁿ = im (αᵖ : D^{p, n} ⟶ D^{0, n})`.

(blueprint: `thm-sp-half-plane-convergence`) -/
theorem convergesTo_halfPlaneFiltration :
    X.ConvergesTo (halfPlaneι h hb) (halfPlaneFiltration h hb) :=
  ⟨halfPlaneConvergenceData h hb⟩

include h hb in
/-- A half-plane couple is regular.

(blueprint: `thm-sp-half-plane-convergence`) -/
theorem isRegular_of_isHalfPlane : X.IsRegular := by
  intro i
  exact ⟨(halfPlaneConvergenceData h hb).stage i.1 i.2,
    fun N hN j ↦ (halfPlaneConvergenceData h hb).d_in i.1 i.2 N hN j⟩

include h in
/-- A half-plane couple is complete.

(blueprint: `thm-sp-half-plane-convergence`) -/
theorem isComplete_of_isHalfPlane : X.IsComplete := by
  rintro ⟨p, n⟩ P hP
  have hr := hP (n - a - p + 1).toNat
  have hz : IsZero (X.D ((p, n) + (((n - a - p + 1).toNat : ℤ), 0))) :=
    h.isZero_D _ _ (by simp; omega)
  simpa only [hz.eq_of_src (X.αPow _ _ _) 0, imageSubobject_zero, le_bot_iff] using hr

include h in
/-- **Stabilisation in a half-plane couple.** The differentials of the `N`-th derived couple
leaving `(p, n)` vanish when `n + b.2 - (p + b.1 + N) < a`, and those arriving at `(p, n)`
vanish when `p - N - b.1 < 0`. -/
theorem derivedIter_d_eq_zero_of_isHalfPlane' (N : ℕ) (p n : ℤ) :
    (n + b.2 - (p + b.1 + N) < a → ∀ j, (X.derivedIter N).d (p, n) j = 0) ∧
      (p - N - b.1 < 0 → ∀ j, (X.derivedIter N).d j (p, n) = 0) := by
  refine ⟨fun hN j ↦ ?_, fun hN j ↦ ?_⟩
  · obtain ⟨π, _, -⟩ := X.exists_epi_comp_ιIter N (p + b.1 + N, n + b.2) ((p, n) + b)
      (by ext <;> simp)
    have hu : IsZero ((X.derivedIter N).D ((p, n) + b)) :=
      IsZero.of_epi π (h.isZero_D _ _ hN)
    rw [d, hu.eq_of_tgt ((X.derivedIter N).f (p, n) ((p, n) + b)) 0, zero_comp]
  · by_cases hj : j + (b + degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ) N) = (p, n)
    · rw [degIter_neg_one_zero] at hj
      obtain rfl : j = (p - N - b.1, n - b.2) := by
        obtain ⟨j₁, j₂⟩ := j
        have h₁ := congrArg _root_.Prod.fst hj
        have h₂ := congrArg _root_.Prod.snd hj
        simp at h₁ h₂
        rw [Prod.mk.injEq]
        constructor <;> omega
      exact (X.isZero_derivedIter_E 0 N (Nat.zero_le _) _
        (h.isZero_E _ _ (Or.inl hN))).eq_of_src _ _
    · exact (X.derivedIter N).shape_d _ _ hj

end HalfPlane

section HalfPlaneTwoOne

variable {X : ExactCouple C ((-1, 0) : ℤ × ℤ) (2, 1) 0} {a : ℤ} (h : X.IsHalfPlane a)

include h in
/-- **Stabilisation in a half-plane couple of type `b = (2, 1)`.** The `N`-th derived couple is
the page `E_r` with `r = N + 2`; writing `q = n - p`, the differentials of `E_r` leaving and
arriving at `(p, n)` vanish as soon as `r > max (q - a + 1) p`.

(blueprint: `thm-sp-half-plane-convergence`) -/
theorem derivedIter_d_eq_zero_of_isHalfPlane (N : ℕ) (p n : ℤ)
    (hN : max (n - p - a + 1) p < N + 2) :
    (∀ j, (X.derivedIter N).d (p, n) j = 0) ∧ (∀ j, (X.derivedIter N).d j (p, n) = 0) := by
  have := X.derivedIter_d_eq_zero_of_isHalfPlane' h N p n
  exact ⟨this.1 (by simp at hN ⊢; omega), this.2 (by simp at hN ⊢; omega)⟩

/-- **The entries of a half-plane couple of type `b = (2, 1)` stabilise.** Writing `q = n - p`,
for `r = N + 2 > max (q - a + 1) p` the entry `E_r^{p, n}` of the page `E_r` (the `N`-th derived
couple) is isomorphic to the graded piece `grᵖ Aⁿ` of the abutment `Aⁿ = D^{0, n}`.

(blueprint: `thm-sp-half-plane-convergence`) -/
noncomputable def halfPlaneDerivedIterEIsoGr (N : ℕ) (p n : ℤ)
    (hN : max (n - p - a + 1) p < N + 2) :
    (X.derivedIter N).E (p, n) ≅ (halfPlaneFiltration h (by norm_num) n).gr p :=
  let c := halfPlaneConvergenceData h (by norm_num)
  have hs (N' : ℕ) (hN' : N ≤ N') :=
    derivedIter_d_eq_zero_of_isHalfPlane h N' p n (by omega)
  (X.derivedIterAddEIso N (p, n) (fun N' hN' ↦ (hs N' hN').1 _)
      (fun N' hN' ↦ (hs N' hN').2 _) (c.stage p n)).symm ≪≫
    c.iso p n (N + c.stage p n) (by omega)

end HalfPlaneTwoOne

end ExactCouple

end CategoryTheory
