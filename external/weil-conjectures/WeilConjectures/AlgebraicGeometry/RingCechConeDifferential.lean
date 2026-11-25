/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingCechConeLinearEquiv

/-! # Differential of the algebraic localization cone

Source: Stacks Project, more-algebra.tex, section-alternating-cech,
its defining alternating differential.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open scoped BigOperators TensorProduct
namespace CategoryTheory

/-- The canonical augmented alternating localization differential.
Source: Stacks Project, more-algebra.tex, section-alternating-cech, formulas (1)--(3).
(auxiliary; not a blueprint node). -/
def ringCechDifferential (A : CommRingCat.{u}) (r : ℕ) (g : Fin r → A) :
    ∀ n : ℕ, ringCechTailTerm A r g n →ₗ[A] ringCechTailTerm A r g (n + 1)
  | 0 => LinearMap.pi (fun _ ↦ (Algebra.ofId A _).toLinearMap)
  | q + 1 => LinearMap.pi (fun t ↦ ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
      ((ringCechFace A g q t j).toLinearMap.comp
        (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t))))

/-- Evaluation of the positive-degree canonical differential.
Source: Stacks Project, more-algebra.tex, section-alternating-cech, formula (3).
(auxiliary; not a blueprint node). -/
theorem ringCechDifferential_succ (A : CommRingCat.{u}) (r : ℕ) (g : Fin r → A)
    (q : ℕ) (x : ringCechTailTerm A r g (q + 1)) (t : Fin (q + 2) ↪o Fin r) :
    ringCechDifferential A r g (q + 1) x t =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
        ringCechFace A g q t j (x ((Fin.succAboveOrderEmb j).trans t)) := by
  simp only [ringCechDifferential, LinearMap.pi_apply, LinearMap.sum_apply,
]
  apply Finset.sum_congr rfl
  intro j _
  rfl

private theorem differential_shift (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A)
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (y : Localization.Away (f 0) ⊗[A] ringCechTailTerm A r (fun i ↦ f i.succ) q)
    (t : Fin (q + 2) ↪o Fin r) :
    ringCechDifferential A (r + 1) f (q + 1)
      (ringCechConeEquiv A r q f (x, y)) (ringCechShift t) =
        ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x t := by
  rw [ringCechDifferential_succ, ringCechDifferential_succ]
  apply Finset.sum_congr rfl
  intro j _
  change (-1 : ℤ) ^ j.val • ringCechFace A (fun i ↦ f i.succ) q t j
    (ringCechConeEquiv A r q f (x, y)
      (ringCechShift ((Fin.succAboveOrderEmb j).trans t))) = _
  rw [ringCechConeEquiv_shift]

private theorem cons_face_succ_zero {q r : ℕ} (t : Fin (q + 1) ↪o Fin r)
    (j : Fin (q + 1)) :
    ((Fin.succAboveOrderEmb j.succ).trans (ringCechCons t)) 0 = 0 := by
  simp [ringCechCons, Fin.succAboveOrderEmb]

private theorem cone_fst_zero_at_cons (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A)
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (t : Fin (q + 1) ↪o Fin (r + 1)) (h : t 0 = 0) :
    ringCechConeEquiv A r q f (x, 0) t = 0 := by
  rw [← cons_ringCechTailPred t h, ringCechConeEquiv_cons, map_zero]
  rfl

private theorem differential_fst_cons (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A)
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (t : Fin (q + 1) ↪o Fin r) :
    ringCechDifferential A (r + 1) f (q + 1)
      (ringCechConeEquiv A r q f (x, 0)) (ringCechCons t) =
        ringCechHeadRight A f t (x t) := by
  rw [ringCechDifferential_succ, Fin.sum_univ_succ]
  have hz (j : Fin (q + 1)) :
      ringCechConeEquiv A r q f (x, 0)
        ((Fin.succAboveOrderEmb j.succ).trans (ringCechCons t)) = 0 :=
    cone_fst_zero_at_cons A r q f x _ (cons_face_succ_zero t j)
  simp only [hz, map_zero, Fin.val_zero, pow_zero, one_smul]
  have hsum : (∑ j : Fin (q + 1), (-1 : ℤ) ^ j.succ.val •
      (0 : Localization.Away (∏ i, f (ringCechCons t i)))) = 0 := by simp
  have hfirst : (ringCechFace A f q (ringCechCons t) 0)
      (ringCechConeEquiv A r q f (x, 0)
        ((Fin.succAboveOrderEmb (0 : Fin (q + 2))).trans (ringCechCons t))) =
        ringCechHeadRight A f t (x t) := by
    change (ringCechFace A f q (ringCechCons t) 0)
      (ringCechConeEquiv A r q f (x, 0) (ringCechShift t)) = _
    rw [ringCechConeEquiv_shift]
    exact congrArg (fun h : Localization.Away (∏ i, f (t i).succ) →ₐ[A]
      Localization.Away (∏ i, f (ringCechCons t i)) ↦ h (x t))
      (ringCechLocMap_unique A _ _ _)
  exact (congrArg₂ (· + ·) hfirst hsum).trans (add_zero _)

private theorem differential_fst (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A)
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1)) :
    ringCechConeEquiv A r (q + 1) f
      (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x, 1 ⊗ₜ[A] x) =
      ringCechDifferential A (r + 1) f (q + 1) (ringCechConeEquiv A r q f (x, 0)) := by
  funext t
  obtain ⟨s, rfl⟩ := (ringCechIndexEquiv (q + 1) r).surjective t
  cases s with
  | inl t =>
    change ringCechConeEquiv A r (q + 1) f
      (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x, 1 ⊗ₜ[A] x)
      (ringCechShift t) = ringCechDifferential A (r + 1) f (q + 1)
        (ringCechConeEquiv A r q f (x, 0)) (ringCechShift t)
    rw [ringCechConeEquiv_shift, differential_shift]
  | inr t =>
    change ringCechConeEquiv A r (q + 1) f
      (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x, 1 ⊗ₜ[A] x)
      (ringCechCons t) = ringCechDifferential A (r + 1) f (q + 1)
        (ringCechConeEquiv A r q f (x, 0)) (ringCechCons t)
    rw [ringCechConeEquiv_cons, ringCechHeadEquiv_succ_tmul, map_one, one_mul,
      differential_fst_cons]

private theorem differential_snd_face (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A) (s : Localization.Away (f 0))
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)) :
    ringCechFace A f (q + 1) (ringCechCons t) j.succ
      (ringCechConeEquiv A r (q + 1) f (0, s ⊗ₜ[A] x)
        ((Fin.succAboveOrderEmb j.succ).trans (ringCechCons t))) =
      ringCechHeadLeft A f t s * ringCechHeadRight A f t
        (ringCechFace A (fun i ↦ f i.succ) q t j
          (x ((Fin.succAboveOrderEmb j).trans t))) := by
  have H (v : Fin (q + 2) ↪o Fin (r + 1))
      (hv : v = ringCechCons ((Fin.succAboveOrderEmb j).trans t))
      (hdiv : (∏ i, f (v i)) ∣ ∏ i, f (ringCechCons t i)) :
      ringCechLocMap A _ _ hdiv
        (ringCechConeEquiv A r (q + 1) f (0, s ⊗ₜ[A] x) v) =
        ringCechHeadLeft A f t s * ringCechHeadRight A f t
          (ringCechFace A (fun i ↦ f i.succ) q t j
            (x ((Fin.succAboveOrderEmb j).trans t))) := by
    subst v
    rw [ringCechConeEquiv_cons, ringCechHeadEquiv_succ_tmul, map_mul]
    let k := ringCechLocMap A _ _ hdiv
    have hL : k.comp (ringCechHeadLeft A f ((Fin.succAboveOrderEmb j).trans t)) =
        ringCechHeadLeft A f t := ringCechLocMap_unique A _ _ _
    have hR : k.comp (ringCechHeadRight A f ((Fin.succAboveOrderEmb j).trans t)) =
        (ringCechHeadRight A f t).comp
          (ringCechFace A (fun i ↦ f i.succ) q t j) := ringCechLocMap_unique A _ _ _
    exact congrArg₂ (· * ·) (AlgHom.congr_fun hL s)
      (AlgHom.congr_fun hR (x ((Fin.succAboveOrderEmb j).trans t)))
  apply H _ (ringCechCons_face_succ t j)

private theorem differential_snd_cons_succ (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A) (s : Localization.Away (f 0))
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (t : Fin (q + 2) ↪o Fin r) :
    ringCechDifferential A (r + 1) f (q + 2)
      (ringCechConeEquiv A r (q + 1) f (0, s ⊗ₜ[A] x)) (ringCechCons t) =
      -ringCechHeadEquiv A r (q + 2) f
        (s ⊗ₜ[A] (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x)) t := by
  rw [ringCechHeadEquiv_succ_tmul]
  have h0 : ringCechConeEquiv A r (q + 1) f (0, s ⊗ₜ[A] x)
      ((Fin.succAboveOrderEmb (0 : Fin (q + 3))).trans (ringCechCons t)) = 0 := by
    exact ringCechConeEquiv_shift A r (q + 1) f 0 (s ⊗ₜ[A] x) t
  calc
    _ = ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.succ.val •
        ringCechFace A f (q + 1) (ringCechCons t) j.succ
          (ringCechConeEquiv A r (q + 1) f (0, s ⊗ₜ[A] x)
            ((Fin.succAboveOrderEmb j.succ).trans (ringCechCons t))) := by
      rw [ringCechDifferential_succ, Fin.sum_univ_succ]
      have hfirst : (-1 : ℤ) ^ (0 : Fin (q + 3)).val •
          ringCechFace A f (q + 1) (ringCechCons t) 0
            (ringCechConeEquiv A r (q + 1) f (0, s ⊗ₜ[A] x)
              ((Fin.succAboveOrderEmb 0).trans (ringCechCons t))) = 0 := by
        rw [h0, map_zero]
        simp only [Fin.val_zero, pow_zero, one_smul]
      exact (congrArg (· + _) hfirst).trans (zero_add _)
    _ = ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.succ.val •
        (ringCechHeadLeft A f t s * ringCechHeadRight A f t
          (ringCechFace A (fun i ↦ f i.succ) q t j
            (x ((Fin.succAboveOrderEmb j).trans t)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [differential_snd_face]
    _ = _ := by
      rw [ringCechDifferential_succ, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, map_zsmul, mul_smul_comm]

private theorem differential_snd_face_zero (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin (r + 1) → A) (s : Localization.Away (f 0)) (x : A)
    (t : Fin 1 ↪o Fin r) :
    ringCechFace A f 0 (ringCechCons t) (1 : Fin 2)
      (ringCechConeEquiv A r 0 f (0, s ⊗ₜ[A] x)
        ((Fin.succAboveOrderEmb (1 : Fin 2)).trans (ringCechCons t))) =
      ringCechHeadLeft A f t s * algebraMap A _ x := by
  have H (v : Fin 1 ↪o Fin (r + 1))
      (hv : v = ringCechCons ((Fin.succAboveOrderEmb (0 : Fin 1)).trans t))
      (hdiv : (∏ i, f (v i)) ∣ ∏ i, f (ringCechCons t i)) :
      ringCechLocMap A _ _ hdiv (ringCechConeEquiv A r 0 f (0, s ⊗ₜ[A] x) v) =
        ringCechHeadLeft A f t s * algebraMap A _ x := by
    subst v
    rw [ringCechConeEquiv_cons, ringCechHeadEquiv_zero_tmul, map_mul, AlgHom.commutes]
    let k := ringCechLocMap A _ _ hdiv
    have hL : k.comp
        (ringCechHeadLeft A f ((Fin.succAboveOrderEmb (0 : Fin 1)).trans t)) =
        ringCechHeadLeft A f t := ringCechLocMap_unique A _ _ _
    exact congrArg (· * algebraMap A _ x) (AlgHom.congr_fun hL s)
  apply H _ (ringCechCons_face_succ t (0 : Fin 1))

private theorem differential_snd_cons_zero (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin (r + 1) → A) (s : Localization.Away (f 0)) (x : A)
    (t : Fin 1 ↪o Fin r) :
    ringCechDifferential A (r + 1) f 1
      (ringCechConeEquiv A r 0 f (0, s ⊗ₜ[A] x)) (ringCechCons t) =
      -ringCechHeadEquiv A r 1 f
        (s ⊗ₜ[A] (ringCechDifferential A r (fun i ↦ f i.succ) 0 x)) t := by
  rw [ringCechHeadEquiv_succ_tmul]
  change _ = -(ringCechHeadLeft A f t s * ringCechHeadRight A f t
    (algebraMap A _ x))
  rw [AlgHom.commutes, ringCechDifferential_succ, Fin.sum_univ_two]
  have h0 : ringCechConeEquiv A r 0 f (0, s ⊗ₜ[A] x)
      ((Fin.succAboveOrderEmb (0 : Fin 2)).trans (ringCechCons t)) = 0 := by
    exact ringCechConeEquiv_shift A r 0 f 0 (s ⊗ₜ[A] x) t
  have hfirst : (-1 : ℤ) ^ (0 : Fin 2).val • ringCechFace A f 0 (ringCechCons t) 0
      (ringCechConeEquiv A r 0 f (0, s ⊗ₜ[A] x)
        ((Fin.succAboveOrderEmb 0).trans (ringCechCons t))) = 0 := by
    rw [h0, map_zero]
    simp only [Fin.val_zero, pow_zero, one_smul]
  have hlast : (-1 : ℤ) ^ (1 : Fin 2).val • ringCechFace A f 0 (ringCechCons t) 1
      (ringCechConeEquiv A r 0 f (0, s ⊗ₜ[A] x)
        ((Fin.succAboveOrderEmb 1).trans (ringCechCons t))) =
        -(ringCechHeadLeft A f t s * algebraMap A _ x) := by
    rw [differential_snd_face_zero]
    simp
  exact (congrArg₂ (· + ·) hfirst hlast).trans (zero_add _)

private theorem differential_snd_tmul (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A) (s : Localization.Away (f 0))
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) q) :
    ringCechConeEquiv A r (q + 1) f
      (0, -TensorProduct.map (LinearMap.id : Localization.Away (f 0) →ₗ[A] _)
        (ringCechDifferential A r (fun i ↦ f i.succ) q) (s ⊗ₜ[A] x)) =
      ringCechDifferential A (r + 1) f (q + 1)
        (ringCechConeEquiv A r q f (0, s ⊗ₜ[A] x)) := by
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  funext t
  obtain ⟨v, rfl⟩ := (ringCechIndexEquiv (q + 1) r).surjective t
  cases v with
  | inl t =>
    change ringCechConeEquiv A r (q + 1) f
      (0, -(s ⊗ₜ[A] (ringCechDifferential A r (fun i ↦ f i.succ) q x)))
      (ringCechShift t) = ringCechDifferential A (r + 1) f (q + 1)
        (ringCechConeEquiv A r q f (0, s ⊗ₜ[A] x)) (ringCechShift t)
    rw [ringCechConeEquiv_shift, differential_shift, map_zero]
  | inr t =>
    change ringCechConeEquiv A r (q + 1) f
      (0, -(s ⊗ₜ[A] (ringCechDifferential A r (fun i ↦ f i.succ) q x)))
      (ringCechCons t) = ringCechDifferential A (r + 1) f (q + 1)
        (ringCechConeEquiv A r q f (0, s ⊗ₜ[A] x)) (ringCechCons t)
    rw [ringCechConeEquiv_cons, map_neg]
    change -ringCechHeadEquiv A r (q + 1) f
      (s ⊗ₜ[A] (ringCechDifferential A r (fun i ↦ f i.succ) q x)) t = _
    symm
    cases q with
    | zero => exact differential_snd_cons_zero A r f s x t
    | succ q => exact differential_snd_cons_succ A r q f s x t

/-- The two-block differential becomes the full alternating differential.
Source: Stacks Project, more-algebra.tex, section-alternating-cech, formulas (2)--(3).
Proof: subsets avoiding zero use the tail differential. On subsets containing zero,
the first face contributes the localized first block. All remaining faces preserve zero;
their indices increase by one, changing the signs. On pure tensors the localization maps
commute by the universal property. Linearity extends the calculation to every tensor.
(auxiliary; not a blueprint node). -/
theorem ringCechConeEquiv_d (A : CommRingCat.{u}) (r q : ℕ)
    (f : Fin (r + 1) → A)
    (x : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 1))
    (y : Localization.Away (f 0) ⊗[A] ringCechTailTerm A r (fun i ↦ f i.succ) q) :
    ringCechConeEquiv A r (q + 1) f
      (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x,
        1 ⊗ₜ[A] x - TensorProduct.map
          (LinearMap.id : Localization.Away (f 0) →ₗ[A] _)
          (ringCechDifferential A r (fun i ↦ f i.succ) q) y) =
      ringCechDifferential A (r + 1) f (q + 1) (ringCechConeEquiv A r q f (x, y)) := by
  let T := TensorProduct.map
    (LinearMap.id : Localization.Away (f 0) →ₗ[A] Localization.Away (f 0))
    (ringCechDifferential A r (fun i ↦ f i.succ) q)
  let E := ringCechConeEquiv A r (q + 1) f
  let F := ringCechConeEquiv A r q f
  let D := ringCechDifferential A (r + 1) f (q + 1)
  have hy : ∀ z, E (0, -T z) = D (F (0, z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s z => exact differential_snd_tmul A r q f s z
    | add z w hz hw =>
      have hp : ((0 : ringCechTailTerm A r (fun i ↦ f i.succ) (q + 2)),
          -T (z + w)) = (0, -T z) + (0, -T w) := by
        rw [map_add, neg_add]
        simp only [Prod.mk_add_mk, zero_add]
      rw [hp, map_add, hz, hw, ← map_add, ← map_add]
      simp only [Prod.mk_add_mk, zero_add]
  have hp : (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x,
      1 ⊗ₜ[A] x - T y) =
      (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x, 1 ⊗ₜ[A] x) +
        (0, -T y) := by
    apply Prod.ext
    · exact (add_zero _).symm
    · exact sub_eq_add_neg _ _
  change E (_, 1 ⊗ₜ[A] x - T y) = D (F (x, y))
  rw [hp, map_add]
  change ringCechConeEquiv A r (q + 1) f
    (ringCechDifferential A r (fun i ↦ f i.succ) (q + 1) x, 1 ⊗ₜ[A] x) +
      E (0, -T y) = _
  rw [differential_fst, hy]
  change D (F (x, 0)) + D (F (0, y)) = _
  rw [← map_add, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

/-- The degree-zero map is the full diagonal localization.
Source: Stacks Project, more-algebra.tex, section-alternating-cech, formula (1).
(auxiliary; not a blueprint node). -/
theorem ringCechConeEquiv_d_zero (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin (r + 1) → A) (x : A) :
    ringCechConeEquiv A r 0 f
      (ringCechDifferential A r (fun i ↦ f i.succ) 0 x, 1 ⊗ₜ[A] x) =
      ringCechDifferential A (r + 1) f 0 x := by
  funext t
  obtain ⟨v, rfl⟩ := (ringCechIndexEquiv 0 r).surjective t
  cases v with
  | inl t =>
    change ringCechConeEquiv A r 0 f
      (ringCechDifferential A r (fun i ↦ f i.succ) 0 x, 1 ⊗ₜ[A] x)
      (ringCechShift t) = _
    rw [ringCechConeEquiv_shift]
    rfl
  | inr t =>
    change ringCechConeEquiv A r 0 f
      (ringCechDifferential A r (fun i ↦ f i.succ) 0 x, 1 ⊗ₜ[A] x)
      (ringCechCons t) = _
    rw [ringCechConeEquiv_cons, ringCechHeadEquiv_zero_tmul, map_one, one_mul]
    rfl

end CategoryTheory
