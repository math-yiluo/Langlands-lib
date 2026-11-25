/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# First quadrant double complexes whose rows are resolutions

Let `K` be a first quadrant double complex in an abelian category, with columns `K.X p` and
horizontal differentials `K.d p (p + 1)`, and let `ε : L ⟶ K.X 0` be a morphism of cochain
complexes such that for every `q` the row
`0 ⟶ L^q ⟶ K^{0, q} ⟶ K^{1, q} ⟶ K^{2, q} ⟶ ⋯`
is exact. Then the composite `L ⟶ K.X 0 ⟶ Tot K` is a quasi-isomorphism.

The proof is the usual staircase argument, carried out with refinements
(`CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`): a cocycle of the total complex
can be pushed, column by column, into the column `0`, where it comes from `L`.

## Main definitions

- `HomologicalComplex₂.totalπ`: the projection from the total complex onto a summand.
- `HomologicalComplex₂.toTotalOfAugmentation`: the morphism `L ⟶ Tot K` induced by `ε`.

## Main statements

- `HomologicalComplex₂.quasiIso_toTotalOfAugmentation`: if the rows of `K` augmented by `L` are
  exact, then `L ⟶ Tot K` is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory Limits Preadditive

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

lemma π_up_nat (p q : ℕ) :
    ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = p + q :=
  rfl

/-- The projection from the degree `n` term of the total complex of a first quadrant double
complex onto the summand `(K.X p).X q` (it vanishes if `p + q ≠ n`). -/
noncomputable def totalπ (n p q : ℕ) : (K.total (ComplexShape.up ℕ)).X n ⟶ (K.X p).X q :=
  K.totalDesc fun p' q' _ ↦ if h : p' = p ∧ q' = q then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0

@[reassoc]
lemma ιTotal_totalπ (p' q' n : ℕ) (h : p' + q' = n) (p q : ℕ) :
    K.ιTotal (ComplexShape.up ℕ) p' q' n h ≫ K.totalπ n p q =
      if h : p' = p ∧ q' = q then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0 := by
  simp [totalπ]

@[reassoc (attr := simp)]
lemma ιTotal_totalπ_self (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ K.totalπ n p q = 𝟙 _ := by
  simp [ιTotal_totalπ]

@[reassoc]
lemma ιTotal_totalπ_of_ne_left (p' q' n : ℕ) (h : p' + q' = n) (p q : ℕ) (hp : p' ≠ p) :
    K.ιTotal (ComplexShape.up ℕ) p' q' n h ≫ K.totalπ n p q = 0 := by
  rw [ιTotal_totalπ, dite_eq_right (fun h ↦ hp h.1)]

@[reassoc]
lemma ιTotal_totalπ_of_ne_right (p' q' n : ℕ) (h : p' + q' = n) (p q : ℕ) (hq : q' ≠ q) :
    K.ιTotal (ComplexShape.up ℕ) p' q' n h ≫ K.totalπ n p q = 0 := by
  rw [ιTotal_totalπ, dite_eq_right (fun h ↦ hq h.2)]

lemma totalπ_eq_zero (n p q : ℕ) (h : p + q ≠ n) : K.totalπ n p q = 0 := by
  ext p' q' h'
  rw [comp_zero, ιTotal_totalπ, dite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact h h'

lemma ε₁_up_nat (p q : ℕ) :
    ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = 1 :=
  rfl

lemma ε₂_up_nat (p q : ℕ) :
    ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) =
      (ComplexShape.up ℕ).ε p :=
  rfl

/-- The decomposition of the identity of a term of the total complex into its summands. -/
lemma sum_totalπ_ιTotal (n : ℕ) :
    ∑ p : Fin (n + 1), K.totalπ n p (n - p) ≫
      K.ιTotal (ComplexShape.up ℕ) p (n - p) n (by rw [π_up_nat]; have := p.isLt; omega) =
      𝟙 _ := by
  ext p' q' h'
  rw [π_up_nat] at h'
  rw [comp_sum, Category.comp_id, Finset.sum_eq_single ⟨p', by omega⟩]
  · obtain rfl : q' = n - p' := by omega
    simp
  · intro p _ hp
    rw [ιTotal_totalπ_of_ne_left_assoc _ _ _ _ _ _ _ (fun h ↦ hp (Fin.ext h.symm)), zero_comp]
  · simp

lemma total_hom_ext_π {A : C} {n : ℕ} {f g : A ⟶ (K.total (ComplexShape.up ℕ)).X n}
    (h : ∀ p q, p + q = n → f ≫ K.totalπ n p q = g ≫ K.totalπ n p q) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← sum_totalπ_ιTotal, comp_sum, comp_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Category.assoc, h p (n - p) (by have := p.isLt; omega), Category.assoc]

/-- The components of the differential of the total complex. -/
lemma ιTotal_d_totalπ (p' q' n : ℕ) (h : p' + q' = n) (p q : ℕ) :
    K.ιTotal (ComplexShape.up ℕ) p' q' n h ≫ (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫
      K.totalπ (n + 1) p q =
      (K.d p' (p' + 1)).f q' ≫ (if h : p' + 1 = p ∧ q' = q then
        (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0) +
      (ComplexShape.up ℕ).ε p' • ((K.X p').d q' (q' + 1) ≫ (if h : p' = p ∧ q' + 1 = q then
        (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0)) := by
  simp only [total_d, comp_add, add_comp, ι_D₁_assoc, ι_D₂_assoc]
  rw [K.d₁_eq _ (show (ComplexShape.up ℕ).Rel p' (p' + 1) from rfl) q' (n + 1)
      (by rw [π_up_nat]; omega),
    K.d₂_eq _ p' (show (ComplexShape.up ℕ).Rel q' (q' + 1) from rfl) (n + 1)
      (by rw [π_up_nat]; omega)]
  simp only [ε₁_up_nat, ε₂_up_nat, one_smul, Linear.units_smul_comp, Category.assoc,
    ιTotal_totalπ]

lemma d_totalπ_succ_succ (n p q : ℕ) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫ K.totalπ (n + 1) (p + 1) (q + 1) =
      K.totalπ n p (q + 1) ≫ (K.d p (p + 1)).f (q + 1) +
        (ComplexShape.up ℕ).ε (p + 1) • (K.totalπ n (p + 1) q ≫ (K.X (p + 1)).d q (q + 1)) := by
  ext p' q' h'
  rw [π_up_nat] at h'
  rw [ιTotal_d_totalπ _ _ _ _ h', comp_add, ιTotal_totalπ_assoc, Linear.comp_units_smul,
    ιTotal_totalπ_assoc]
  split_ifs <;> first | omega | (simp; done) | (exfalso; tauto) |
    (obtain ⟨rfl, rfl⟩ := ‹p' = _ ∧ q' = _›; simp)

lemma d_totalπ_succ_zero (n p : ℕ) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫ K.totalπ (n + 1) (p + 1) 0 =
      K.totalπ n p 0 ≫ (K.d p (p + 1)).f 0 := by
  ext p' q' h'
  rw [π_up_nat] at h'
  rw [ιTotal_d_totalπ _ _ _ _ h', ιTotal_totalπ_assoc]
  split_ifs <;> first | omega | (simp; done) | (exfalso; tauto) |
    (obtain ⟨rfl, rfl⟩ := ‹p' = _ ∧ q' = _›; simp)

lemma d_totalπ_zero_succ (n q : ℕ) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫ K.totalπ (n + 1) 0 (q + 1) =
      K.totalπ n 0 q ≫ (K.X 0).d q (q + 1) := by
  ext p' q' h'
  rw [π_up_nat] at h'
  rw [ιTotal_d_totalπ _ _ _ _ h', ιTotal_totalπ_assoc]
  split_ifs <;> first | omega | (simp; done) | (exfalso; tauto) |
    (obtain ⟨rfl, rfl⟩ := ‹p' = _ ∧ q' = _›; simp)

lemma d_totalπ_zero_zero (n : ℕ) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫ K.totalπ (n + 1) 0 0 = 0 := by
  rw [totalπ_eq_zero _ _ _ _ (by omega), comp_zero]


section Staircase

/-- A morphism to the total complex in degree `m` all of whose components in the columns
`p ≥ j` vanish. -/
def VanishesFrom {A : C} {m : ℕ} (x : A ⟶ (K.total (ComplexShape.up ℕ)).X m) (j : ℕ) : Prop :=
  ∀ p q, j ≤ p → x ≫ K.totalπ m p q = 0

variable {K}

lemma vanishesFrom_of_lt {A : C} {m : ℕ} (x : A ⟶ (K.total (ComplexShape.up ℕ)).X m) (j : ℕ)
    (hj : m < j) : K.VanishesFrom x j := fun p q hp ↦ by
  rw [totalπ_eq_zero _ _ _ _ (by omega), comp_zero]

lemma vanishesFrom_comp {A A' : C} {m : ℕ} (π : A' ⟶ A)
    {x : A ⟶ (K.total (ComplexShape.up ℕ)).X m} {j : ℕ} (hx : K.VanishesFrom x j) :
    K.VanishesFrom (π ≫ x) j := fun p q hp ↦ by
  rw [Category.assoc, hx p q hp, comp_zero]

/-- A morphism whose components vanish in the columns `p ≥ 1` factors through the column `0`. -/
lemma eq_totalπ_ιTotal_of_vanishesFrom_one {A : C} {m : ℕ}
    {x : A ⟶ (K.total (ComplexShape.up ℕ)).X m} (hx : K.VanishesFrom x 1) :
    x = (x ≫ K.totalπ m 0 m) ≫ K.ιTotal (ComplexShape.up ℕ) 0 m m (by rw [π_up_nat]; omega) := by
  refine K.total_hom_ext_π fun p q hpq ↦ ?_
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = m := by omega
    simp
  · rw [hx p q (by omega), Category.assoc, ιTotal_totalπ_of_ne_left _ _ _ _ _ _ _ (Ne.symm hp),
      comp_zero]

/-- The component in the column `p + 1` of the differential of a morphism to the total complex
whose components vanish in the column `p + 1`. -/
lemma comp_d_totalπ_succ {A : C} {n : ℕ} (x : A ⟶ (K.total (ComplexShape.up ℕ)).X n) (p q : ℕ)
    (hx : ∀ q', x ≫ K.totalπ n (p + 1) q' = 0) :
    x ≫ (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫ K.totalπ (n + 1) (p + 1) q =
      (x ≫ K.totalπ n p q) ≫ (K.d p (p + 1)).f q := by
  obtain _ | q := q
  · rw [d_totalπ_succ_zero, Category.assoc]
  · rw [d_totalπ_succ_succ, comp_add, Linear.comp_units_smul]
    simp only [← Category.assoc, hx, zero_comp, smul_zero, add_zero]

lemma comp_d_totalπ_zero {A : C} {n : ℕ} (x : A ⟶ (K.total (ComplexShape.up ℕ)).X n) :
    x ≫ (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫ K.totalπ (n + 1) 0 (n + 1) =
      (x ≫ K.totalπ n 0 n) ≫ (K.X 0).d n (n + 1) := by
  rw [d_totalπ_zero_succ, Category.assoc]

variable (hrow : ∀ p q, (ShortComplex.mk ((K.d p (p + 1)).f q) ((K.d (p + 1) (p + 2)).f q)
  (K.d_f_comp_d_f _ _ _ q)).Exact)

include hrow in
/-- One step of the staircase: if the components of `x` vanish in the columns `≥ k + 2` and the
component of `d x` in the column `k + 2` vanishes, then up to refinement and a coboundary the
components of `x` vanish in the columns `≥ k + 1`. -/
lemma exists_vanishesFrom_step {A : C} {m k : ℕ} (hk : k ≤ m)
    (x : A ⟶ (K.total (ComplexShape.up ℕ)).X (m + 1)) (hx : K.VanishesFrom x (k + 2))
    (hdx : x ≫ (K.total (ComplexShape.up ℕ)).d (m + 1) (m + 2) ≫
      K.totalπ (m + 2) (k + 2) (m - k) = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (w : A' ⟶ (K.total (ComplexShape.up ℕ)).X m),
      K.VanishesFrom (π ≫ x - w ≫ (K.total (ComplexShape.up ℕ)).d m (m + 1)) (k + 1) := by
  rw [comp_d_totalπ_succ x (k + 1) _ (fun q' ↦ hx _ _ le_rfl)] at hdx
  obtain ⟨A', π, hπ, z, hz⟩ := (hrow k (m - k)).exact_up_to_refinements _ hdx
  dsimp at z hz
  refine ⟨A', π, hπ, z ≫ K.ιTotal (ComplexShape.up ℕ) k (m - k) m
    (by rw [π_up_nat]; omega), fun p q hp ↦ ?_⟩
  rw [sub_comp, Category.assoc, Category.assoc, Category.assoc, ιTotal_d_totalπ,
    dite_eq_right (show ¬ (k = p ∧ m - k + 1 = q) by omega)]
  simp only [comp_zero, smul_zero, add_zero]
  by_cases hp' : p = k + 1 ∧ m - k = q
  · obtain ⟨rfl, rfl⟩ := hp'
    rw [dite_eq_left ⟨rfl, rfl⟩, hz]
    simp
  · rw [dite_eq_right (fun h ↦ hp' ⟨h.1.symm, h.2⟩), comp_zero, comp_zero, sub_zero]
    by_cases hp'' : p = k + 1
    · subst hp''
      rw [totalπ_eq_zero _ _ _ _ (by omega), comp_zero, comp_zero]
    · rw [hx p q (by omega), comp_zero]

include hrow in
/-- The staircase: if the components of `d x` vanish in the columns `p ≥ 2`, then up to
refinement and a coboundary the components of `x` vanish in the columns `p ≥ 1`. -/
lemma exists_vanishesFrom_one {A : C} {m : ℕ}
    (x : A ⟶ (K.total (ComplexShape.up ℕ)).X m)
    (hdx : K.VanishesFrom (x ≫ (K.total (ComplexShape.up ℕ)).d m (m + 1)) 2) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (w : A' ⟶ (K.total (ComplexShape.up ℕ)).X (m - 1)),
      K.VanishesFrom (π ≫ x - w ≫ (K.total (ComplexShape.up ℕ)).d (m - 1) m) 1 := by
  obtain _ | m := m
  · exact ⟨A, 𝟙 A, inferInstance, 0, by simpa using vanishesFrom_of_lt x 1 (by omega)⟩
  suffices H : ∀ (j : ℕ) {A : C} (x : A ⟶ (K.total (ComplexShape.up ℕ)).X (m + 1)),
      K.VanishesFrom (x ≫ (K.total (ComplexShape.up ℕ)).d (m + 1) (m + 2)) 2 →
      K.VanishesFrom x (j + 1) →
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (w : A' ⟶ (K.total (ComplexShape.up ℕ)).X m),
        K.VanishesFrom (π ≫ x - w ≫ (K.total (ComplexShape.up ℕ)).d m (m + 1)) 1 from
    H (m + 1) x hdx (vanishesFrom_of_lt x _ (by omega))
  intro j
  induction j with
  | zero =>
    intro A x _ hx
    exact ⟨A, 𝟙 A, inferInstance, 0, by simpa using hx⟩
  | succ j ih =>
    intro A x hdx hx
    by_cases hj : j ≤ m
    · obtain ⟨A₁, π₁, hπ₁, w₁, hw₁⟩ := exists_vanishesFrom_step hrow hj x hx (by
        rw [← Category.assoc]
        exact hdx _ _ (by omega))
      obtain ⟨A₂, π₂, hπ₂, w₂, hw₂⟩ := ih (π₁ ≫ x - w₁ ≫ (K.total _).d m (m + 1)) (by
        rw [sub_comp, Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
          sub_zero]
        exact vanishesFrom_comp π₁ hdx) hw₁
      refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, π₂ ≫ w₁ + w₂, ?_⟩
      convert hw₂ using 1
      simp only [comp_sub, add_comp, Category.assoc]
      abel
    · exact ih x hdx (vanishesFrom_of_lt x _ (by omega))

end Staircase

variable {L : CochainComplex C ℕ} (ε : L ⟶ K.X 0) (hε : ε ≫ K.d 0 1 = 0)

lemma comp_f_d_f_eq_zero (hε : ε ≫ K.d 0 1 = 0) (q : ℕ) : ε.f q ≫ (K.d 0 1).f q = 0 := by
  rw [← HomologicalComplex.comp_f, hε, HomologicalComplex.zero_f]

/-- The morphism from `L` to the total complex of `K` induced by a morphism `ε : L ⟶ K.X 0`
such that `ε ≫ K.d 0 1 = 0`. -/
noncomputable def toTotalOfAugmentation (hε : ε ≫ K.d 0 1 = 0) :
    L ⟶ K.total (ComplexShape.up ℕ) where
  f n := ε.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by rw [π_up_nat]; omega)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    have h0 : ε.f i ≫ (K.d 0 1).f i = 0 := by
      rw [← HomologicalComplex.comp_f, hε, HomologicalComplex.zero_f]
    refine K.total_hom_ext_π fun p q hpq ↦ ?_
    simp only [Category.assoc, ιTotal_d_totalπ, ιTotal_totalπ, comp_add, Linear.comp_units_smul]
    split_ifs <;> first | omega | (exfalso; tauto) | simp [reassoc_of% h0]

@[reassoc (attr := simp)]
lemma toTotalOfAugmentation_f_totalπ_zero (n : ℕ) :
    (K.toTotalOfAugmentation ε hε).f n ≫ K.totalπ n 0 n = ε.f n := by
  simp [toTotalOfAugmentation]

lemma vanishesFrom_toTotalOfAugmentation {A : C} {n : ℕ} (x : A ⟶ L.X n) :
    K.VanishesFrom (x ≫ (K.toTotalOfAugmentation ε hε).f n) 1 := fun p q hp ↦ by
  simp only [toTotalOfAugmentation, Category.assoc]
  rw [ιTotal_totalπ_of_ne_left _ _ _ _ _ _ _ (by omega), comp_zero, comp_zero]

variable {K ε hε}

variable (h₀ : ∀ q, Mono (ε.f q))
  (h₁ : ∀ q, (ShortComplex.mk (ε.f q) ((K.d 0 1).f q)
    (K.comp_f_d_f_eq_zero ε hε q)).Exact)
  (hrow : ∀ p q, (ShortComplex.mk ((K.d p (p + 1)).f q) ((K.d (p + 1) (p + 2)).f q)
    (K.d_f_comp_d_f _ _ _ q)).Exact)

include h₁ in
/-- A morphism to the total complex whose components vanish in the columns `p ≥ 1` and whose
differential has a vanishing component in the column `1` comes, up to refinement, from `L`. -/
lemma exists_eq_comp_ε {A : C} {m : ℕ} {x : A ⟶ (K.total (ComplexShape.up ℕ)).X m}
    (hx : K.VanishesFrom x 1)
    (hdx : x ≫ (K.total (ComplexShape.up ℕ)).d m (m + 1) ≫ K.totalπ (m + 1) 1 m = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (l : A' ⟶ L.X m),
      π ≫ x ≫ K.totalπ m 0 m = l ≫ ε.f m := by
  rw [comp_d_totalπ_succ x 0 m (fun q' ↦ hx _ _ le_rfl)] at hdx
  exact (h₁ m).exact_up_to_refinements _ hdx

include h₀ h₁ hrow in
/-- **Rows which are resolutions.** If the rows `0 ⟶ L^q ⟶ K^{0, q} ⟶ K^{1, q} ⟶ ⋯` of a first
quadrant double complex `K` augmented by `ε : L ⟶ K.X 0` are exact, then the induced morphism
`L ⟶ Tot K` is a quasi-isomorphism. -/
theorem quasiIso_toTotalOfAugmentation : QuasiIso (K.toTotalOfAugmentation ε hε) := by
  have : ∀ q, Mono (ε.f q) := h₀
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap (K.toTotalOfAugmentation ε hε) n) := by
    rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ (n - 1) n (n + 1)
      (by obtain _ | n := n <;> simp) (by simp)]
    intro A x₂ hx₂ y₁ hy₁
    obtain _ | m := n
    · refine ⟨A, 𝟙 A, inferInstance, 0, ?_⟩
      have : x₂ ≫ ε.f 0 = 0 := by
        rw [← toTotalOfAugmentation_f_totalπ_zero K ε hε, ← Category.assoc, hy₁,
          HomologicalComplex.shape _ _ _ (by simp), comp_zero, zero_comp]
      have hx : x₂ = 0 := (cancel_mono (ε.f 0)).1 (by rw [this, zero_comp])
      simp [hx]
    · let y : A ⟶ (K.total (ComplexShape.up ℕ)).X m := y₁
      have hy : y ≫ (K.total (ComplexShape.up ℕ)).d m (m + 1) =
          x₂ ≫ (K.toTotalOfAugmentation ε hε).f (m + 1) := hy₁.symm
      obtain ⟨A₁, π₁, hπ₁, w, hw⟩ := exists_vanishesFrom_one hrow y (by
        rw [hy]
        exact fun p q hp ↦ vanishesFrom_toTotalOfAugmentation K ε hε x₂ p q (by omega))
      set y' := π₁ ≫ y - w ≫ (K.total (ComplexShape.up ℕ)).d (m - 1) m
      have hdy' : y' ≫ (K.total (ComplexShape.up ℕ)).d m (m + 1) =
          π₁ ≫ x₂ ≫ (K.toTotalOfAugmentation ε hε).f (m + 1) := by
        simp only [y', sub_comp, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
          sub_zero, hy]
      obtain ⟨A₂, π₂, hπ₂, l, hl⟩ := exists_eq_comp_ε (hε := hε) h₁ hw (by
        rw [← Category.assoc, hdy']
        simp only [Category.assoc]
        rw [← Category.assoc x₂, vanishesFrom_toTotalOfAugmentation K ε hε x₂ 1 m le_rfl,
          comp_zero])
      refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, l, ?_⟩
      have e1 := comp_d_totalπ_zero y'
      rw [← Category.assoc, hdy', Category.assoc, Category.assoc,
        toTotalOfAugmentation_f_totalπ_zero] at e1
      rw [← cancel_mono (ε.f (m + 1))]
      calc ((π₂ ≫ π₁) ≫ x₂) ≫ ε.f (m + 1) =
            π₂ ≫ (y' ≫ K.totalπ m 0 m) ≫ (K.X 0).d m (m + 1) := by
            rw [← e1]
            simp only [Category.assoc]
        _ = (l ≫ L.d m (m + 1)) ≫ ε.f (m + 1) := by
            rw [← Category.assoc, hl, Category.assoc, HomologicalComplex.Hom.comm,
              Category.assoc]
  have hepi : Epi (HomologicalComplex.homologyMap (K.toTotalOfAugmentation ε hε) n) := by
    rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ (n - 1) n (n + 1)
      (by obtain _ | n := n <;> simp) (by simp)]
    intro A y₂ hy₂
    obtain ⟨A₁, π₁, hπ₁, w, hw⟩ := exists_vanishesFrom_one hrow y₂ (by
      rw [hy₂]
      exact fun p q _ ↦ zero_comp)
    set x' := π₁ ≫ y₂ - w ≫ (K.total (ComplexShape.up ℕ)).d (n - 1) n
    have hdx' : x' ≫ (K.total (ComplexShape.up ℕ)).d n (n + 1) = 0 := by
      simp [x', hy₂]
    obtain ⟨A₂, π₂, hπ₂, l, hl⟩ := exists_eq_comp_ε (hε := hε) h₁ hw (by
      rw [← Category.assoc, hdx', zero_comp])
    refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, l, ?_, π₂ ≫ w, ?_⟩
    · rw [← cancel_mono (ε.f (n + 1)), zero_comp]
      have e1 := comp_d_totalπ_zero x'
      rw [← Category.assoc, hdx', zero_comp] at e1
      calc (l ≫ L.d n (n + 1)) ≫ ε.f (n + 1) = (l ≫ ε.f n) ≫ (K.X 0).d n (n + 1) := by
            rw [Category.assoc, ← HomologicalComplex.Hom.comm, Category.assoc]
        _ = 0 := by
            rw [← hl, Category.assoc, ← e1, comp_zero]
    · have hx' := eq_totalπ_ιTotal_of_vanishesFrom_one hw
      have : π₂ ≫ x' = l ≫ (K.toTotalOfAugmentation ε hε).f n := by
        rw [hx', ← Category.assoc, hl]
        simp [toTotalOfAugmentation]
      simp only [x', comp_sub] at this
      rw [Category.assoc, ← sub_eq_iff_eq_add, ← this, Category.assoc]
  exact isIso_of_mono_of_epi _

end HomologicalComplex₂
