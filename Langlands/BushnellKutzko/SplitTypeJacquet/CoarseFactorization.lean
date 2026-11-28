import Langlands.BushnellKutzko.SplitTypeJacquet.IntegralOrder
import Langlands.Group.GL.Basic
import Langlands.BushnellKutzko.SplittingBasis

/-! # The coarse two-block parabolic of a standard order and its Iwahori factorization

For a block function `blk : ι → ℕ` and a cut `j`, the indices split into the late indices
`j ≤ blk p` and the early indices. Listing the late indices first, matrices become `2 × 2`
block matrices. The corner with late rows and early columns lies below the block diagonal. -/

open Matrix ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF

section TwoBlock

variable {F : Type uF} [Field F] {T R : Type*} [Fintype T] [DecidableEq T]
  [Fintype R] [DecidableEq R]

/-- Upper unipotent `2 × 2` block matrices. -/
def upperHom : Multiplicative (Matrix T R F) →* GL (T ⊕ R) F where
  toFun X := ⟨fromBlocks 1 (Multiplicative.toAdd X) 0 1,
    fromBlocks 1 (-Multiplicative.toAdd X) 0 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  map_one' := by ext1; simp
  map_mul' X Y := by ext1; simp [fromBlocks_multiply, add_comm]

/-- Lower unipotent `2 × 2` block matrices. -/
def lowerHom : Multiplicative (Matrix R T F) →* GL (T ⊕ R) F where
  toFun X := ⟨fromBlocks 1 0 (Multiplicative.toAdd X) 1,
    fromBlocks 1 0 (-Multiplicative.toAdd X) 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  map_one' := by ext1; simp
  map_mul' X Y := by ext1; simp [fromBlocks_multiply, add_comm]

/-- Block diagonal `2 × 2` block matrices. -/
def leviHom : GL T F × GL R F →* GL (T ⊕ R) F where
  toFun AD := ⟨fromBlocks (AD.1 : Matrix T T F) 0 0 (AD.2 : Matrix R R F),
    fromBlocks ((AD.1⁻¹ : GL T F) : Matrix T T F) 0 0 ((AD.2⁻¹ : GL R F) : Matrix R R F),
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  map_one' := by ext1; simp
  map_mul' X Y := by ext1; simp [fromBlocks_multiply]

@[simp] theorem coe_upperHom (X : Matrix T R F) :
    ((upperHom (Multiplicative.ofAdd X) : GL (T ⊕ R) F) : Matrix (T ⊕ R) (T ⊕ R) F) =
      fromBlocks 1 X 0 1 := rfl

@[simp] theorem coe_lowerHom (X : Matrix R T F) :
    ((lowerHom (Multiplicative.ofAdd X) : GL (T ⊕ R) F) : Matrix (T ⊕ R) (T ⊕ R) F) =
      fromBlocks 1 0 X 1 := rfl

@[simp] theorem coe_leviHom (A : GL T F) (D : GL R F) :
    ((leviHom (A, D) : GL (T ⊕ R) F) : Matrix (T ⊕ R) (T ⊕ R) F) =
      fromBlocks (A : Matrix T T F) 0 0 (D : Matrix R R F) := rfl

theorem leviHom_conj_upperHom (A : GL T F) (D : GL R F) (X : Matrix T R F) :
    leviHom (A, D) * upperHom (Multiplicative.ofAdd X) * (leviHom (A, D))⁻¹ =
      upperHom (Multiplicative.ofAdd
        ((A : Matrix T T F) * X * ((D⁻¹ : GL R F) : Matrix R R F))) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext1
  simp [fromBlocks_multiply]

theorem leviHom_conj_lowerHom (A : GL T F) (D : GL R F) (X : Matrix R T F) :
    leviHom (A, D) * lowerHom (Multiplicative.ofAdd X) * (leviHom (A, D))⁻¹ =
      lowerHom (Multiplicative.ofAdd
        ((D : Matrix R R F) * X * ((A⁻¹ : GL T F) : Matrix T T F))) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext1
  simp [fromBlocks_multiply]

/-- An invertible block diagonal matrix is in the image of `leviHom`. -/
theorem mem_range_leviHom {g : GL (T ⊕ R) F} {A : Matrix T T F} {S : Matrix R R F}
    (hg : (g : Matrix (T ⊕ R) (T ⊕ R) F) = fromBlocks A 0 0 S) : g ∈ leviHom.range := by
  set M' := ((g⁻¹ : GL (T ⊕ R) F) : Matrix (T ⊕ R) (T ⊕ R) F)
  have h1 : (g : Matrix (T ⊕ R) (T ⊕ R) F) * M' = 1 := by rw [← Units.val_mul]; simp
  have h2 : M' * (g : Matrix (T ⊕ R) (T ⊕ R) F) = 1 := by rw [← Units.val_mul]; simp
  rw [← fromBlocks_toBlocks M', hg, fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj] at h1 h2
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h1 h2
  let Au : GL T F := ⟨A, M'.toBlocks₁₁, h1.1, h2.1⟩
  let Su : GL R F := ⟨S, M'.toBlocks₂₂, h1.2.2.2, h2.2.2.2⟩
  exact ⟨(Au, Su), Units.ext (by rw [coe_leviHom, hg])⟩

end TwoBlock

section Coarse

variable {F : Type uF} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι] (blk : ι → ℕ) (j : ℕ)

/-- The late indices `j ≤ blk p`. -/
abbrev Late := {p : ι // j ≤ blk p}

/-- The early indices. -/
abbrev Early := {p : ι // ¬ j ≤ blk p}

/-- The indices split into the late and the early ones. -/
def coarseEquiv : Late blk j ⊕ Early blk j ≃ ι := Equiv.sumCompl _

variable (F) in
/-- Matrices as `2 × 2` block matrices, late indices first. -/
def coarseReindex : GL ι F ≃* GL (Late blk j ⊕ Early blk j) F :=
  Langlands.GeneralLinear.reindex (coarseEquiv blk j).symm

variable {blk j}

theorem coe_coarseReindex_symm_apply (g : GL (Late blk j ⊕ Early blk j) F) (p q : ι) :
    (((coarseReindex F blk j).symm g : GL ι F) : Matrix ι ι F) p q =
      (g : Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F)
        ((coarseEquiv blk j).symm p) ((coarseEquiv blk j).symm q) := rfl

theorem coe_coarseReindex_apply (g : GL ι F) :
    ((coarseReindex F blk j g : GL (Late blk j ⊕ Early blk j) F) :
        Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) =
      (g : Matrix ι ι F).submatrix (coarseEquiv blk j) (coarseEquiv blk j) := rfl

variable (F blk j)

/-- The corner with late rows and early columns: the unipotent radical of the coarse
parabolic opposite to the standard one. -/
def coarseN : Subgroup (GL ι F) :=
  (upperHom (F := F) (T := Late blk j) (R := Early blk j)).range.comap
    (coarseReindex F blk j).toMonoidHom

/-- The coarse block diagonal subgroup. -/
def coarseM : Subgroup (GL ι F) :=
  (leviHom (F := F) (T := Late blk j) (R := Early blk j)).range.comap
    (coarseReindex F blk j).toMonoidHom

/-- The corner with early rows and late columns. -/
def coarseNbar : Subgroup (GL ι F) :=
  (lowerHom (F := F) (T := Late blk j) (R := Early blk j)).range.comap
    (coarseReindex F blk j).toMonoidHom

variable {F blk j}

theorem coarseM_le_normalizer :
    coarseM F blk j ≤ Subgroup.normalizer (coarseN F blk j : Set (GL ι F)) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  obtain ⟨⟨A, D⟩, hAD⟩ := hm
  have hAD' : coarseReindex F blk j m = leviHom (A, D) := hAD.symm
  intro x
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨Multiplicative.ofAdd ((A : Matrix (Late blk j) (Late blk j) F) *
      Multiplicative.toAdd X *
        ((D⁻¹ : GL (Early blk j) F) : Matrix (Early blk j) (Early blk j) F)), ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul, map_inv, hAD']
      at hX ⊢
    rw [← hX]
    exact (leviHom_conj_upperHom A D (Multiplicative.toAdd X)).symm
  · rintro ⟨X, hX⟩
    refine ⟨Multiplicative.ofAdd (((A⁻¹ : GL (Late blk j) F) :
      Matrix (Late blk j) (Late blk j) F) * Multiplicative.toAdd X *
        (D : Matrix (Early blk j) (Early blk j) F)), ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul, map_inv, hAD']
      at hX ⊢
    have hinv : (leviHom (A, D))⁻¹ = leviHom (A⁻¹, D⁻¹) := by
      rw [← map_inv]; rfl
    have h2 : coarseReindex F blk j x =
        leviHom (A⁻¹, D⁻¹) * upperHom X * (leviHom (A⁻¹, D⁻¹))⁻¹ := by
      rw [← hinv, inv_inv, hX]; group
    have h3 := leviHom_conj_upperHom (A⁻¹) (D⁻¹) (Multiplicative.toAdd X)
    rw [inv_inv] at h3
    rw [h2]
    exact h3.symm

end Coarse

section CoarseValued

variable {F : Type uF} [Field F] [ValuativeRel F] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {blk : ι → ℕ} {j : ℕ}

omit [Field F] [ValuativeRel F] [Fintype ι] [DecidableEq ι] in
/-- Entries of a coarse block matrix, by cases on the blocks. -/
theorem coarse_entry
    (M : Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) (p q : ι) :
    M ((coarseEquiv blk j).symm p) ((coarseEquiv blk j).symm q) =
      if hp : j ≤ blk p then
        (if hq : j ≤ blk q then M (.inl ⟨p, hp⟩) (.inl ⟨q, hq⟩)
          else M (.inl ⟨p, hp⟩) (.inr ⟨q, hq⟩))
      else
        (if hq : j ≤ blk q then M (.inr ⟨p, hp⟩) (.inl ⟨q, hq⟩)
          else M (.inr ⟨p, hp⟩) (.inr ⟨q, hq⟩)) := by
  by_cases hp : j ≤ blk p <;> by_cases hq : j ≤ blk q <;>
    simp [coarseEquiv, hp, hq, Equiv.sumCompl_symm_apply_of_pos,
      Equiv.sumCompl_symm_apply_of_neg]

/-- An element of the late-early corner with entries in the maximal ideal lies in `J1`. -/
theorem coarse_upper_mem_J1 {Y : Matrix (Late blk j) (Early blk j) F}
    (hY : ∀ i k, valuation F (Y i k) < 1) :
    (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Y)) ∈ J1 F blk := by
  have key : ∀ Y : Matrix (Late blk j) (Early blk j) F, (∀ i k, valuation F (Y i k) < 1) →
      InRad blk ((((coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd Y)) :
        GL ι F) : Matrix ι ι F) - 1) := by
    intro Y hY p q
    rw [Matrix.sub_apply, coe_coarseReindex_symm_apply, coe_upperHom,
      coarse_entry (fromBlocks 1 Y 0 1) p q]
    by_cases hp : j ≤ blk p <;> by_cases hq : j ≤ blk q
    · simp only [hp, hq, dite_true, fromBlocks_apply₁₁]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq,
          Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
        simp
    · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₁₂]
      rw [Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hp)), sub_zero]
      exact ⟨(hY _ _).le, fun _ => hY _ _⟩
    · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₂₁]
      rw [Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hq))]
      simp
    · simp only [hp, hq, dite_false, fromBlocks_apply₂₂]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq,
          Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
        simp
  refine mem_J1_of_inRad (key Y hY) ?_
  rw [← map_inv, ← map_inv]
  exact key (-Y) fun i k => by simpa using hY i k

/-- An element of the early-late corner with integral entries lies in `J1`. -/
theorem coarse_lower_mem_J1 {X : Matrix (Early blk j) (Late blk j) F}
    (hX : ∀ i k, valuation F (X i k) ≤ 1) :
    (coarseReindex F blk j).symm (lowerHom (Multiplicative.ofAdd X)) ∈ J1 F blk := by
  have key : ∀ X : Matrix (Early blk j) (Late blk j) F, (∀ i k, valuation F (X i k) ≤ 1) →
      InRad blk ((((coarseReindex F blk j).symm (lowerHom (Multiplicative.ofAdd X)) :
        GL ι F) : Matrix ι ι F) - 1) := by
    intro X hX p q
    rw [Matrix.sub_apply, coe_coarseReindex_symm_apply, coe_lowerHom,
      coarse_entry (fromBlocks 1 0 X 1) p q]
    by_cases hp : j ≤ blk p <;> by_cases hq : j ≤ blk q
    · simp only [hp, hq, dite_true, fromBlocks_apply₁₁]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq,
          Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
        simp
    · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₁₂]
      rw [Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hp))]
      simp
    · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₂₁]
      rw [Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hq)), sub_zero]
      refine ⟨hX _ _, fun h => ?_⟩
      exfalso
      omega
    · simp only [hp, hq, dite_false, fromBlocks_apply₂₂]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq,
          Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
        simp
  refine mem_J1_of_inRad (key X hX) ?_
  rw [← map_inv, ← map_inv]
  exact key (-X) fun i k => by simpa using hX i k

omit [ValuativeRel F] in
theorem upper_entry {g : GL ι F} {Y : Matrix (Late blk j) (Early blk j) F}
    (hg : upperHom (Multiplicative.ofAdd Y) = coarseReindex F blk j g)
    (i : Late blk j) (k : Early blk j) :
    Y i k = (g : Matrix ι ι F) i.1 k.1 := by
  have h := congrArg (fun x : GL (Late blk j ⊕ Early blk j) F =>
    (x : Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) (.inl i) (.inr k)) hg
  simpa [coe_coarseReindex_apply, coarseEquiv] using h

omit [ValuativeRel F] in
theorem lower_entry {g : GL ι F} {X : Matrix (Early blk j) (Late blk j) F}
    (hg : lowerHom (Multiplicative.ofAdd X) = coarseReindex F blk j g)
    (i : Early blk j) (k : Late blk j) :
    X i k = (g : Matrix ι ι F) i.1 k.1 := by
  have h := congrArg (fun x : GL (Late blk j ⊕ Early blk j) F =>
    (x : Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) (.inr i) (.inl k)) hg
  simpa [coe_coarseReindex_apply, coarseEquiv] using h

/-- **Iwahori factorization of `J0`** relative to the coarse parabolic, with unipotent factors in
`J1`. -/
theorem coarse_factor {x : GL ι F} (hx : x ∈ J0 F blk) :
    ∃ l ∈ J1 F blk ⊓ coarseNbar F blk j, ∃ m ∈ J0 F blk ⊓ coarseM F blk j,
      ∃ u ∈ J1 F blk ⊓ coarseN F blk j, x = l * m * u := by
  classical
  set M : Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F :=
    ((coarseReindex F blk j x : GL (Late blk j ⊕ Early blk j) F) :
      Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) with hM
  set M' : Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F :=
    ((coarseReindex F blk j x⁻¹ : GL (Late blk j ⊕ Early blk j) F) :
      Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) with hM'
  have hMe : ∀ a b, M a b = (x : Matrix ι ι F) (coarseEquiv blk j a) (coarseEquiv blk j b) :=
    fun a b => rfl
  have hM'e : ∀ a b, M' a b = ((x⁻¹ : GL ι F) : Matrix ι ι F)
      (coarseEquiv blk j a) (coarseEquiv blk j b) := fun a b => rfl
  have hMM : M * M' = 1 := by
    rw [hM, hM', ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  set A' := M'.toBlocks₁₁
  set C' := M'.toBlocks₂₁
  have hint : ∀ a b, valuation F (M a b) ≤ 1 := fun a b => by rw [hMe]; exact (hx.1 _ _).1
  have hint' : ∀ a b, valuation F (M' a b) ≤ 1 := fun a b => by
    rw [hM'e]; exact (hx.2 _ _).1
  have hB : ∀ a b, valuation F (B a b) < 1 := by
    intro a b
    change valuation F (M (.inl a) (.inr b)) < 1
    rw [hMe]
    refine (hx.1 _ _).2 ?_
    simp only [coarseEquiv, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    have ha := a.2
    have hb := b.2
    omega
  have hAA : A * A' + B * C' = 1 := by
    have h := hMM
    rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks M', fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
    exact h.1
  have hsub : ∀ a b, valuation F ((A * A') a b -
      (1 : Matrix (Late blk j) (Late blk j) F) a b) < 1 := by
    intro a b
    have : (A * A') a b - (1 : Matrix (Late blk j) (Late blk j) F) a b = -((B * C') a b) := by
      rw [← hAA]; simp
    rw [this, Valuation.map_neg]
    exact lt_one_mul_int hB (fun a b => hint' _ _) a b
  obtain ⟨G1, hG1, hG1inv⟩ := exists_intGL_of_sub_one (A * A') hsub
  set Ainv := A' * ((G1⁻¹ : GL (Late blk j) F) : Matrix (Late blk j) (Late blk j) F) with hAinv
  have hAAinv : A * Ainv = 1 := by
    rw [hAinv, ← Matrix.mul_assoc, ← hG1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAinvA : Ainv * A = 1 := mul_eq_one_comm.mp hAAinv
  have hAinvint : ∀ a b, valuation F (Ainv a b) ≤ 1 :=
    int_mul_le_one (fun a b => hint' _ _) hG1inv
  let _ : Invertible A := ⟨Ainv, hAinvA, hAAinv⟩
  have hLU := Matrix.fromBlocks_eq_of_invertible₁₁ A B C D
  have hinvOf : ⅟A = Ainv := rfl
  rw [hinvOf] at hLU
  set l : GL ι F :=
    (coarseReindex F blk j).symm (lowerHom (Multiplicative.ofAdd (C * Ainv))) with hl
  set u : GL ι F :=
    (coarseReindex F blk j).symm (upperHom (Multiplicative.ofAdd (Ainv * B))) with hu
  have hlJ : l ∈ J1 F blk :=
    coarse_lower_mem_J1 (int_mul_le_one (fun a b => hint _ _) hAinvint)
  have huJ : u ∈ J1 F blk := coarse_upper_mem_J1 (int_mul_lt_one hAinvint hB)
  refine ⟨l, ⟨hlJ, ⟨Multiplicative.ofAdd (C * Ainv), ?_⟩⟩, l⁻¹ * x * u⁻¹,
    ⟨(J0 F blk).mul_mem ((J0 F blk).mul_mem ((J0 F blk).inv_mem (J1_le_J0 hlJ)) hx)
      ((J0 F blk).inv_mem (J1_le_J0 huJ)), ?_⟩, u,
    ⟨huJ, ⟨Multiplicative.ofAdd (Ainv * B), ?_⟩⟩, by group⟩
  · rw [hl]; simp
  · change coarseReindex F blk j (l⁻¹ * x * u⁻¹) ∈ leviHom.range
    refine mem_range_leviHom (A := A) (S := D - C * Ainv * B) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hl, hu, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, Units.val_mul, Units.val_mul]
    change ((lowerHom (Multiplicative.ofAdd (C * Ainv)))⁻¹ :
      GL (Late blk j ⊕ Early blk j) F).val * M *
      ((upperHom (Multiplicative.ofAdd (Ainv * B)))⁻¹ :
        GL (Late blk j ⊕ Early blk j) F).val = _
    rw [← Matrix.fromBlocks_toBlocks M, hLU]
    rw [show fromBlocks 1 0 (C * Ainv) 1 =
        ((lowerHom (Multiplicative.ofAdd (C * Ainv)) : GL (Late blk j ⊕ Early blk j) F) :
          Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) from rfl,
      show fromBlocks 1 (Ainv * B) 0 1 =
        ((upperHom (Multiplicative.ofAdd (Ainv * B)) : GL (Late blk j ⊕ Early blk j) F) :
          Matrix (Late blk j ⊕ Early blk j) (Late blk j ⊕ Early blk j) F) from rfl]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · rw [hu]; simp

end CoarseValued

end Langlands.BushnellKutzko.SplitTypeJacquet
