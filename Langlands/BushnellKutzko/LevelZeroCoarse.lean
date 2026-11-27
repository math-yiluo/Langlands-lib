import Langlands.BushnellKutzko.LevelZeroPrincipal
import Langlands.Group.GL.Basic
import Langlands.BushnellKutzko.SplittingBasis

/-! # The first-block parabolic and its Iwahori factorization -/

open Matrix ValuativeRel Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF uV uW uT uR

section TwoBlock

variable {F : Type uF} [Field F] {T : Type uT} {R : Type uR} [Fintype T] [DecidableEq T]
  [Fintype R] [DecidableEq R]

/-- Upper unipotent `2 × 2` block matrices. -/
def upperHom : Multiplicative (Matrix T R F) →* GL (T ⊕ R) F where
  toFun X := ⟨fromBlocks 1 (Multiplicative.toAdd X) 0 1, fromBlocks 1 (-Multiplicative.toAdd X) 0 1,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  map_one' := by ext1; simp
  map_mul' X Y := by ext1; simp [fromBlocks_multiply, add_comm]

/-- Lower unipotent `2 × 2` block matrices. -/
def lowerHom : Multiplicative (Matrix R T F) →* GL (T ⊕ R) F where
  toFun X := ⟨fromBlocks 1 0 (Multiplicative.toAdd X) 1, fromBlocks 1 0 (-Multiplicative.toAdd X) 1,
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
      upperHom (Multiplicative.ofAdd ((A : Matrix T T F) * X * ((D⁻¹ : GL R F) : Matrix R R F))) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext1
  simp [fromBlocks_multiply]

theorem leviHom_conj_lowerHom (A : GL T F) (D : GL R F) (X : Matrix R T F) :
    leviHom (A, D) * lowerHom (Multiplicative.ofAdd X) * (leviHom (A, D))⁻¹ =
      lowerHom (Multiplicative.ofAdd ((D : Matrix R R F) * X * ((A⁻¹ : GL T F) : Matrix T T F))) := by
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

variable {F : Type uF} [Field F] {e f : ℕ}

/-- The indices of the first block. -/
abbrev TopIx (f : ℕ) (he : 0 < e) := {p : Fin f × Fin e // p.2 = ⟨0, he⟩}

/-- The indices of the other blocks. -/
abbrev RstIx (f : ℕ) (he : 0 < e) := {p : Fin f × Fin e // ¬ p.2 = ⟨0, he⟩}

/-- The indices split into the first block and the others. -/
def coarseEquiv (f : ℕ) (he : 0 < e) : TopIx f he ⊕ RstIx f he ≃ Fin f × Fin e :=
  Equiv.sumCompl _

variable (F) in
/-- Matrices as `2 × 2` block matrices for the splitting into the first block and the others. -/
def coarseReindex (f : ℕ) (he : 0 < e) :
    GL (Fin f × Fin e) F ≃* GL (TopIx f he ⊕ RstIx f he) F :=
  Langlands.GeneralLinear.reindex (coarseEquiv f he).symm

theorem coe_coarseReindex_symm_apply (he : 0 < e) (g : GL (TopIx f he ⊕ RstIx f he) F)
    (p q : Fin f × Fin e) :
    (((coarseReindex F f he).symm g : GL (Fin f × Fin e) F) : Matrix _ _ F) p q =
      (g : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F)
        ((coarseEquiv f he).symm p) ((coarseEquiv f he).symm q) := rfl

theorem coe_coarseReindex_apply (he : 0 < e) (g : GL (Fin f × Fin e) F) :
    ((coarseReindex F f he g : GL (TopIx f he ⊕ RstIx f he) F) :
        Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F) =
      (g : Matrix (Fin f × Fin e) (Fin f × Fin e) F).submatrix (coarseEquiv f he)
        (coarseEquiv f he) := rfl

variable (F) in
/-- The unipotent radical of the coarse upper parabolic. -/
def coarseN (f : ℕ) (he : 0 < e) : Subgroup (GL (Fin f × Fin e) F) :=
  (upperHom (F := F) (T := TopIx f he) (R := RstIx f he)).range.comap
    (coarseReindex F f he).toMonoidHom

variable (F) in
/-- The Levi subgroup of the coarse upper parabolic. -/
def coarseM (f : ℕ) (he : 0 < e) : Subgroup (GL (Fin f × Fin e) F) :=
  (leviHom (F := F) (T := TopIx f he) (R := RstIx f he)).range.comap
    (coarseReindex F f he).toMonoidHom

variable (F) in
/-- The unipotent radical of the opposite coarse parabolic. -/
def coarseNbar (f : ℕ) (he : 0 < e) : Subgroup (GL (Fin f × Fin e) F) :=
  (lowerHom (F := F) (T := TopIx f he) (R := RstIx f he)).range.comap
    (coarseReindex F f he).toMonoidHom

theorem coarseM_le_normalizer (he : 0 < e) :
    coarseM F f he ≤ Subgroup.normalizer (coarseN F f he : Set (GL (Fin f × Fin e) F)) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  obtain ⟨⟨A, D⟩, hAD⟩ := hm
  have hAD' : coarseReindex F f he m = leviHom (A, D) := hAD.symm
  intro x
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨Multiplicative.ofAdd ((A : Matrix (TopIx f he) (TopIx f he) F) *
      Multiplicative.toAdd X * ((D⁻¹ : GL (RstIx f he) F) : Matrix (RstIx f he) (RstIx f he) F)), ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul, map_inv, hAD']
      at hX ⊢
    rw [← hX]
    exact (leviHom_conj_upperHom A D (Multiplicative.toAdd X)).symm
  · rintro ⟨X, hX⟩
    refine ⟨Multiplicative.ofAdd (((A⁻¹ : GL (TopIx f he) F) : Matrix (TopIx f he) (TopIx f he) F) *
      Multiplicative.toAdd X * (D : Matrix (RstIx f he) (RstIx f he) F)), ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul, map_inv, hAD']
      at hX ⊢
    have hinv : (leviHom (A, D))⁻¹ = leviHom (A⁻¹, D⁻¹) := by
      rw [← map_inv]; rfl
    have h2 : coarseReindex F f he x =
        leviHom (A⁻¹, D⁻¹) * upperHom X * (leviHom (A⁻¹, D⁻¹))⁻¹ := by
      rw [← hinv, inv_inv, hX]; group
    have h3 := leviHom_conj_upperHom (A⁻¹) (D⁻¹) (Multiplicative.toAdd X)
    rw [inv_inv] at h3
    rw [h2]
    exact h3.symm

end Coarse

section CoarseValued

variable {F : Type uF} [Field F] [ValuativeRel F] {e f : ℕ}

private theorem one_apply_sub_val {ι : Type*} [DecidableEq ι] (p q : ι) :
    valuation F ((1 : Matrix ι ι F) p q) ≤ 1 := by
  by_cases h : p = q <;> simp [h, Matrix.one_apply]

omit [Field F] [ValuativeRel F] in
/-- Entries of a coarse block matrix, by cases on the blocks. -/
theorem coarse_entry (he : 0 < e) (M : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F)
    (p q : Fin f × Fin e) :
    M ((coarseEquiv f he).symm p) ((coarseEquiv f he).symm q) =
      if hp : p.2 = ⟨0, he⟩ then
        (if hq : q.2 = ⟨0, he⟩ then M (.inl ⟨p, hp⟩) (.inl ⟨q, hq⟩)
          else M (.inl ⟨p, hp⟩) (.inr ⟨q, hq⟩))
      else
        (if hq : q.2 = ⟨0, he⟩ then M (.inr ⟨p, hp⟩) (.inl ⟨q, hq⟩)
          else M (.inr ⟨p, hp⟩) (.inr ⟨q, hq⟩)) := by
  by_cases hp : p.2 = ⟨0, he⟩ <;> by_cases hq : q.2 = ⟨0, he⟩ <;>
    simp [coarseEquiv, hp, hq, Equiv.sumCompl_symm_apply_of_pos,
      Equiv.sumCompl_symm_apply_of_neg]

/-- An upper coarse unipotent element with entries in the maximal ideal lies in `U^1(𝔄)`. -/
theorem coarse_upper_mem_J1 (he : 0 < e) {Y : Matrix (TopIx f he) (RstIx f he) F}
    (hY : ∀ i j, valuation F (Y i j) < 1) :
    (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd Y)) ∈ J1 F e f := by
  have key : ∀ Y : Matrix (TopIx f he) (RstIx f he) F, (∀ i j, valuation F (Y i j) < 1) →
      InRad ((((coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd Y)) :
        GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) - 1) := by
    intro Y hY p q
    rw [Matrix.sub_apply, coe_coarseReindex_symm_apply, coe_upperHom,
      coarse_entry he (fromBlocks 1 Y 0 1) p q]
    by_cases hp : p.2 = ⟨0, he⟩ <;> by_cases hq : q.2 = ⟨0, he⟩
    · simp only [hp, hq, dite_true, fromBlocks_apply₁₁]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
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
      · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
        simp
  refine mem_J1_of_inRad (key Y hY) ?_
  rw [← map_inv, ← map_inv]
  exact key (-Y) fun i j => by simpa using hY i j

/-- A lower coarse unipotent element with integral entries lies in `U^1(𝔄)`. -/
theorem coarse_lower_mem_J1 (he : 0 < e) {X : Matrix (RstIx f he) (TopIx f he) F}
    (hX : ∀ i j, valuation F (X i j) ≤ 1) :
    (coarseReindex F f he).symm (lowerHom (Multiplicative.ofAdd X)) ∈ J1 F e f := by
  have key : ∀ X : Matrix (RstIx f he) (TopIx f he) F, (∀ i j, valuation F (X i j) ≤ 1) →
      InRad ((((coarseReindex F f he).symm (lowerHom (Multiplicative.ofAdd X)) :
        GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) - 1) := by
    intro X hX p q
    rw [Matrix.sub_apply, coe_coarseReindex_symm_apply, coe_lowerHom,
      coarse_entry he (fromBlocks 1 0 X 1) p q]
    by_cases hp : p.2 = ⟨0, he⟩ <;> by_cases hq : q.2 = ⟨0, he⟩
    · simp only [hp, hq, dite_true, fromBlocks_apply₁₁]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
        simp
    · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₁₂]
      rw [Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hp))]
      simp
    · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₂₁]
      rw [Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hq)), sub_zero]
      refine ⟨hX _ _, fun h => ?_⟩
      exfalso
      have h1 : (q.2 : ℕ) = 0 := by rw [hq]
      have h2 : (p.2 : ℕ) ≠ 0 := fun h' => hp (Fin.ext h')
      rw [Fin.le_def] at h
      omega
    · simp only [hp, hq, dite_false, fromBlocks_apply₂₂]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
        simp
  refine mem_J1_of_inRad (key X hX) ?_
  rw [← map_inv, ← map_inv]
  exact key (-X) fun i j => by simpa using hX i j

end CoarseValued

section CoarseContraction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e f : ℕ} {ϖ : 𝒪[F]}

/-- The scalar `ϖ` on the first block. -/
def topScalar (hϖ : Irreducible ϖ) (he : 0 < e) : GL (TopIx f he) F :=
  ⟨Matrix.diagonal fun _ => (ϖ : F), Matrix.diagonal fun _ => (ϖ : F)⁻¹,
    by rw [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (uniformizer_ne_zero' hϖ),
      Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (uniformizer_ne_zero' hϖ),
      Matrix.diagonal_one]⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coarseReindex_aElt (hϖ : Irreducible ϖ) (he : 0 < e) :
    coarseReindex F f he (aElt hϖ he) = leviHom (topScalar hϖ he, 1) := by
  ext1
  rw [coe_coarseReindex_apply, coe_leviHom]
  ext i j
  have hd : ∀ p q : Fin f × Fin e,
      ((aElt (f := f) hϖ he : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) p q =
      if p = q then scaleDiag ϖ he p else 0 := fun p q => by
    change Matrix.diagonal (scaleDiag ϖ he) p q = _
    exact Matrix.diagonal_apply _ _ _
  rcases i with ⟨p, hp⟩ | ⟨p, hp⟩ <;> rcases j with ⟨q, hq⟩ | ⟨q, hq⟩
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inl, fromBlocks_apply₁₁,
      hd, topScalar]
    rw [Matrix.diagonal_apply]
    by_cases h : p = q
    · subst h; simp [scaleDiag, hp]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (congrArg Subtype.val h'))]
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, fromBlocks_apply₁₂, hd, Matrix.zero_apply]
    rw [ite_eq_right (fun h => hq (by rw [← h]; exact hp))]
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inl,
      Equiv.sumCompl_apply_inr, fromBlocks_apply₂₁, hd, Matrix.zero_apply]
    rw [ite_eq_right (fun h => hp (by rw [h]; exact hq))]
  · simp only [Matrix.submatrix_apply, coarseEquiv, Equiv.sumCompl_apply_inr, fromBlocks_apply₂₂,
      hd, Units.val_one]
    by_cases h : p = q
    · subst h; simp [scaleDiag, hp]
    · rw [ite_eq_right h, Matrix.one_apply_ne (fun h' => h (congrArg Subtype.val h'))]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem aElt_mem_coarseM (hϖ : Irreducible ϖ) (he : 0 < e) :
    aElt hϖ he ∈ coarseM F f he :=
  ⟨(topScalar hϖ he, 1), (coarseReindex_aElt hϖ he).symm⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem aElt_conj_upper (hϖ : Irreducible ϖ) (he : 0 < e) (Y : Matrix (TopIx f he) (RstIx f he) F) :
    aElt hϖ he * (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd Y)) *
        (aElt hϖ he)⁻¹ =
      (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd ((ϖ : F) • Y))) := by
  apply (coarseReindex F f he).injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    coarseReindex_aElt, leviHom_conj_upperHom]
  congr 2
  ext i j
  simp [topScalar, Matrix.diagonal_mul]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem aElt_inv_conj_lower (hϖ : Irreducible ϖ) (he : 0 < e)
    (X : Matrix (RstIx f he) (TopIx f he) F) :
    (aElt hϖ he)⁻¹ * (coarseReindex F f he).symm (lowerHom (Multiplicative.ofAdd X)) *
        aElt hϖ he =
      (coarseReindex F f he).symm (lowerHom (Multiplicative.ofAdd ((ϖ : F) • X))) := by
  apply (coarseReindex F f he).injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    coarseReindex_aElt]
  have hinv : (leviHom (topScalar (f := f) hϖ he, (1 : GL (RstIx f he) F)))⁻¹ =
      leviHom ((topScalar (f := f) hϖ he)⁻¹, 1) := by rw [← map_inv]; rfl
  rw [hinv, show leviHom (topScalar (f := f) hϖ he, (1 : GL (RstIx f he) F)) =
      (leviHom ((topScalar (f := f) hϖ he)⁻¹, (1 : GL (RstIx f he) F)))⁻¹ by
    rw [← map_inv]; simp, leviHom_conj_lowerHom]
  congr 2
  ext i j
  simp [topScalar, Matrix.mul_diagonal, mul_comm]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem aElt_inv_conj_levi (hϖ : Irreducible ϖ) (he : 0 < e) {m : GL (Fin f × Fin e) F}
    (hm : m ∈ coarseM F f he) : (aElt hϖ he)⁻¹ * m * aElt hϖ he = m := by
  obtain ⟨⟨A, D⟩, hAD⟩ := hm
  have hAD' : coarseReindex F f he m = leviHom (A, D) := hAD.symm
  apply (coarseReindex F f he).injective
  rw [map_mul, map_mul, map_inv, coarseReindex_aElt, hAD', ← map_inv, ← map_mul, ← map_mul]
  congr 1
  simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_one, one_mul, mul_one, Prod.mk.injEq, and_true]
  ext1
  ext i j
  simp [topScalar, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (ϖ : F)⁻¹, mul_assoc,
    mul_inv_cancel₀ (uniformizer_ne_zero' hϖ)]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem int_mul_le_one {ι κ μ : Type*} [Fintype κ] {A : Matrix ι κ F} {B : Matrix κ μ F}
    (hA : ∀ i j, valuation F (A i j) ≤ 1) (hB : ∀ i j, valuation F (B i j) ≤ 1) (i : ι) (j : μ) :
    valuation F ((A * B) i j) ≤ 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun c _ => by rw [map_mul]; exact mul_le_one' (hA i c) (hB c j)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem int_mul_lt_one {ι κ μ : Type*} [Fintype κ] {A : Matrix ι κ F} {B : Matrix κ μ F}
    (hA : ∀ i j, valuation F (A i j) ≤ 1) (hB : ∀ i j, valuation F (B i j) < 1) (i : ι) (j : μ) :
    valuation F ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun c _ => ?_
  rw [map_mul]
  calc valuation F (A i c) * valuation F (B c j) ≤ 1 * valuation F (B c j) :=
        mul_le_mul' (hA i c) le_rfl
    _ < 1 := by rw [one_mul]; exact hB c j

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lt_one_mul_int {ι κ μ : Type*} [Fintype κ] {A : Matrix ι κ F} {B : Matrix κ μ F}
    (hA : ∀ i j, valuation F (A i j) < 1) (hB : ∀ i j, valuation F (B i j) ≤ 1) (i : ι) (j : μ) :
    valuation F ((A * B) i j) < 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_lt _ one_ne_zero fun c _ => ?_
  rw [map_mul]
  calc valuation F (A i c) * valuation F (B c j) ≤ valuation F (A i c) * 1 :=
        mul_le_mul' le_rfl (hB c j)
    _ < 1 := by rw [mul_one]; exact hA i c

/-- **Iwahori factorization of `U(𝔄)`** relative to the coarse parabolic, with unipotent factors
in `U^1(𝔄)`. -/
theorem coarse_factor (he : 0 < e) {x : GL (Fin f × Fin e) F} (hx : x ∈ J0 F e f) :
    ∃ l ∈ J1 F e f ⊓ coarseNbar F f he, ∃ m ∈ J0 F e f ⊓ coarseM F f he,
      ∃ u ∈ J1 F e f ⊓ coarseN F f he, x = l * m * u := by
  classical
  set M : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F :=
    ((coarseReindex F f he x : GL (TopIx f he ⊕ RstIx f he) F) :
      Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F) with hM
  set M' : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F :=
    ((coarseReindex F f he x⁻¹ : GL (TopIx f he ⊕ RstIx f he) F) :
      Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F) with hM'
  have hMe : ∀ i j, M i j = (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F)
      (coarseEquiv f he i) (coarseEquiv f he j) := fun i j => rfl
  have hM'e : ∀ i j, M' i j = ((x⁻¹ : GL (Fin f × Fin e) F) :
      Matrix (Fin f × Fin e) (Fin f × Fin e) F) (coarseEquiv f he i) (coarseEquiv f he j) :=
    fun i j => rfl
  have hMM : M * M' = 1 := by
    rw [hM, hM', ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  set A' := M'.toBlocks₁₁
  set C' := M'.toBlocks₂₁
  have hint : ∀ i j, valuation F (M i j) ≤ 1 := fun i j => by rw [hMe]; exact (hx.1 _ _).1
  have hint' : ∀ i j, valuation F (M' i j) ≤ 1 := fun i j => by rw [hM'e]; exact (hx.2 _ _).1
  have hB : ∀ i j, valuation F (B i j) < 1 := by
    intro i j
    change valuation F (M (.inl i) (.inr j)) < 1
    rw [hMe]
    refine (hx.1 _ _).2 ?_
    simp only [coarseEquiv, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    rw [i.2, Fin.lt_def]
    have := j.2
    simp only [Fin.ext_iff] at this
    simp only; omega
  have hAA : A * A' + B * C' = 1 := by
    have h := hMM
    rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks M', fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h
    exact h.1
  have hsub : ∀ i j, valuation F ((A * A') i j - (1 : Matrix (TopIx f he) (TopIx f he) F) i j) < 1 := by
    intro i j
    have : (A * A') i j - (1 : Matrix (TopIx f he) (TopIx f he) F) i j = -((B * C') i j) := by
      rw [← hAA]; simp
    rw [this, Valuation.map_neg]
    exact lt_one_mul_int hB (fun i j => hint' _ _) i j
  obtain ⟨G1, hG1, hG1inv⟩ := exists_isIntGL_of_sub_one (A * A') hsub
  set Ainv := A' * ((G1⁻¹ : GL (TopIx f he) F) : Matrix (TopIx f he) (TopIx f he) F) with hAinv
  have hAAinv : A * Ainv = 1 := by
    rw [hAinv, ← Matrix.mul_assoc, ← hG1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAinvA : Ainv * A = 1 := mul_eq_one_comm.mp hAAinv
  have hAinvint : ∀ i j, valuation F (Ainv i j) ≤ 1 :=
    int_mul_le_one (fun i j => hint' _ _) hG1inv
  let _ : Invertible A := ⟨Ainv, hAinvA, hAAinv⟩
  have hLU := Matrix.fromBlocks_eq_of_invertible₁₁ A B C D
  have hinvOf : ⅟A = Ainv := rfl
  rw [hinvOf] at hLU
  set l : GL (Fin f × Fin e) F :=
    (coarseReindex F f he).symm (lowerHom (Multiplicative.ofAdd (C * Ainv))) with hl
  set u : GL (Fin f × Fin e) F :=
    (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd (Ainv * B))) with hu
  have hlJ : l ∈ J1 F e f :=
    coarse_lower_mem_J1 he (int_mul_le_one (fun i j => hint _ _) hAinvint)
  have huJ : u ∈ J1 F e f := coarse_upper_mem_J1 he (int_mul_lt_one hAinvint hB)
  refine ⟨l, ⟨hlJ, ⟨Multiplicative.ofAdd (C * Ainv), ?_⟩⟩, l⁻¹ * x * u⁻¹,
    ⟨(J0 F e f).mul_mem ((J0 F e f).mul_mem ((J0 F e f).inv_mem (J1_le_J0 hlJ)) hx)
      ((J0 F e f).inv_mem (J1_le_J0 huJ)), ?_⟩, u,
    ⟨huJ, ⟨Multiplicative.ofAdd (Ainv * B), ?_⟩⟩, by group⟩
  · rw [hl]; simp
  · change coarseReindex F f he (l⁻¹ * x * u⁻¹) ∈ leviHom.range
    refine mem_range_leviHom (A := A) (S := D - C * Ainv * B) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hl, hu, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, Units.val_mul, Units.val_mul]
    change ((lowerHom (Multiplicative.ofAdd (C * Ainv)))⁻¹ : GL (TopIx f he ⊕ RstIx f he) F).val * M *
      ((upperHom (Multiplicative.ofAdd (Ainv * B)))⁻¹ : GL (TopIx f he ⊕ RstIx f he) F).val = _
    rw [← Matrix.fromBlocks_toBlocks M, hLU]
    rw [show fromBlocks 1 0 (C * Ainv) 1 =
        ((lowerHom (Multiplicative.ofAdd (C * Ainv)) : GL (TopIx f he ⊕ RstIx f he) F) : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F) from rfl,
      show fromBlocks 1 (Ainv * B) 0 1 =
        ((upperHom (Multiplicative.ofAdd (Ainv * B)) : GL (TopIx f he ⊕ RstIx f he) F) : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F) from rfl]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  · rw [hu]; simp

theorem exists_pow_mul_lt_one (hϖ : Irreducible ϖ) (c : F) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → valuation F ((ϖ : F) ^ s * c) < 1 := by
  by_cases hc : c = 0
  · exact ⟨0, fun s _ => by simp [hc]⟩
  obtain ⟨t, w, hw⟩ := exists_eq_zpow_mul_unit hϖ hc
  refine ⟨(1 - t).toNat, fun s hs => ?_⟩
  have hn : ((s : ℤ) + t).toNat ≥ 1 := by omega
  set n := ((s : ℤ) + t).toNat with hn'
  have hpow : (ϖ : F) ^ s * c = (ϖ : F) * ((ϖ : F) ^ (n - 1) * ((w : 𝒪[F]) : F)) := by
    rw [hw, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ (uniformizer_ne_zero' hϖ),
      ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, ← zpow_natCast]
    congr 2
    omega
  rw [hpow]
  refine val_uniformizer_mul_lt_one hϖ ?_
  rw [map_mul, map_pow]
  exact mul_le_one' (pow_le_one' (val_uniformizer_lt_one hϖ).le _) (w : 𝒪[F]).2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem aElt_pow_conj_upper (hϖ : Irreducible ϖ) (he : 0 < e) (r : ℕ)
    (Y : Matrix (TopIx f he) (RstIx f he) F) :
    aElt hϖ he ^ r * (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd Y)) *
        (aElt hϖ he ^ r)⁻¹ =
      (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd ((ϖ : F) ^ r • Y))) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e1 : aElt hϖ he ^ (r + 1) *
        (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd Y)) *
          (aElt hϖ he ^ (r + 1))⁻¹ =
        aElt hϖ he * (aElt hϖ he ^ r *
          (coarseReindex F f he).symm (upperHom (Multiplicative.ofAdd Y)) *
            (aElt hϖ he ^ r)⁻¹) * (aElt hϖ he)⁻¹ := by group
    rw [e1, ih, aElt_conj_upper, smul_smul, pow_succ']

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem upper_entry {he : 0 < e} {g : GL (Fin f × Fin e) F}
    {Y : Matrix (TopIx f he) (RstIx f he) F}
    (hg : upperHom (Multiplicative.ofAdd Y) = coarseReindex F f he g)
    (i : TopIx f he) (j : RstIx f he) :
    Y i j = (g : Matrix (Fin f × Fin e) (Fin f × Fin e) F) i.1 j.1 := by
  have h := congrArg (fun x : GL (TopIx f he ⊕ RstIx f he) F =>
    (x : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F) (.inl i) (.inr j)) hg
  simpa [coe_coarseReindex_apply, coarseEquiv] using h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem lower_entry {he : 0 < e} {g : GL (Fin f × Fin e) F}
    {X : Matrix (RstIx f he) (TopIx f he) F}
    (hg : lowerHom (Multiplicative.ofAdd X) = coarseReindex F f he g)
    (i : RstIx f he) (j : TopIx f he) :
    X i j = (g : Matrix (Fin f × Fin e) (Fin f × Fin e) F) i.1 j.1 := by
  have h := congrArg (fun x : GL (TopIx f he ⊕ RstIx f he) F =>
    (x : Matrix (TopIx f he ⊕ RstIx f he) (TopIx f he ⊕ RstIx f he) F) (.inr i) (.inl j)) hg
  simpa [coe_coarseReindex_apply, coarseEquiv] using h

/-- The Iwahori factorization of `U(𝔄)` restricts to `U^1(𝔄)`. -/
theorem coarse_J1_factor (he : 0 < e)
    (K : OpenSubgroup (GL (Fin f × Fin e) F)) (hKJ : K.toSubgroup = J1 F e f) :
    ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ coarseNbar F f he, ∃ m ∈ K.toSubgroup ⊓ coarseM F f he,
      ∃ u ∈ K.toSubgroup ⊓ coarseN F f he, k = l * m * u := by
  intro k hk
  have hkJ : k ∈ J1 F e f := hKJ ▸ (show k ∈ K.toSubgroup from hk)
  obtain ⟨l, ⟨hl1, hl2⟩, m, ⟨_, hm2⟩, u, ⟨hu1, hu2⟩, hlmu⟩ := coarse_factor he (J1_le_J0 hkJ)
  have hmJ : m ∈ J1 F e f := by
    have hm : m = l⁻¹ * k * u⁻¹ := by rw [hlmu]; group
    rw [hm]
    exact (J1 F e f).mul_mem ((J1 F e f).mul_mem ((J1 F e f).inv_mem hl1) hkJ)
      ((J1 F e f).inv_mem hu1)
  rw [hKJ]
  exact ⟨l, ⟨hl1, hl2⟩, m, ⟨hmJ, hm2⟩, u, ⟨hu1, hu2⟩, hlmu⟩

omit [IsNonarchimedeanLocalField F] in
/-- `diag(ϖ, 1, …, 1)` is a weak Iwahori contraction for `U^1(𝔄)` relative to
the parabolic of the first block. -/
theorem coarse_isWeakIwahoriContraction (hϖ : Irreducible ϖ) (he : 0 < e)
    (K : OpenSubgroup (GL (Fin f × Fin e) F)) (hKJ : K.toSubgroup = J1 F e f) :
    IsWeakIwahoriContraction K (coarseN F f he) (coarseM F f he) (coarseNbar F f he)
      (aElt hϖ he) := by
  have hJK : ∀ x, x ∈ K.toSubgroup ↔ x ∈ J1 F e f := fun x => by rw [hKJ]
  refine ⟨aElt_mem_coarseM hϖ he, ?_, ?_, ?_⟩
  · rintro u ⟨hu1, ⟨Y, hY⟩⟩
    have hYint : ∀ i j, valuation F (Multiplicative.toAdd Y i j) ≤ 1 := by
      intro i j
      rw [upper_entry (Y := Multiplicative.toAdd Y) hY]
      exact (((hJK u).mp hu1).1.1 _ _).1
    have hu : u = (coarseReindex F f he).symm (upperHom Y) := by
      rw [hY]; simp
    rw [hu]
    have := aElt_conj_upper hϖ he (Multiplicative.toAdd Y)
    simp only [ofAdd_toAdd] at this
    rw [this]
    refine ⟨(hJK _).mpr (coarse_upper_mem_J1 he fun i j => ?_),
      ⟨Multiplicative.ofAdd ((ϖ : F) • Multiplicative.toAdd Y), by simp⟩⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    exact val_uniformizer_mul_lt_one hϖ (hYint i j)
  · rintro m ⟨hm1, hm2⟩
    rw [aElt_inv_conj_levi hϖ he hm2]
    exact ⟨hm1, hm2⟩
  · rintro l ⟨hl1, ⟨X, hX⟩⟩
    have hXint : ∀ i j, valuation F (Multiplicative.toAdd X i j) ≤ 1 := by
      intro i j
      rw [lower_entry (X := Multiplicative.toAdd X) hX]
      exact (((hJK l).mp hl1).1.1 _ _).1
    have hl : l = (coarseReindex F f he).symm (lowerHom X) := by
      rw [hX]; simp
    rw [hl]
    have := aElt_inv_conj_lower hϖ he (Multiplicative.toAdd X)
    simp only [ofAdd_toAdd] at this
    rw [this]
    refine ⟨(hJK _).mpr (coarse_lower_mem_J1 he fun i j => ?_),
      ⟨Multiplicative.ofAdd ((ϖ : F) • Multiplicative.toAdd X), by simp⟩⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (val_uniformizer_mul_lt_one hϖ (hXint i j)).le

/-- Powers of the diagonal contraction carry each upper unipotent into `U^1(𝔄)`. -/
theorem coarse_exhaust (hϖ : Irreducible ϖ) (he : 0 < e)
    (K : OpenSubgroup (GL (Fin f × Fin e) F)) (hKJ : K.toSubgroup = J1 F e f) :
    ∀ x ∈ coarseN F f he, ∃ r : ℕ, aElt hϖ he ^ r * x * (aElt hϖ he ^ r)⁻¹ ∈ K := by
  rintro x ⟨Y, hY⟩
  have hx : x = (coarseReindex F f he).symm (upperHom Y) := by
    rw [hY]; simp
  have hent : ∀ ij : TopIx f he × RstIx f he, ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
      valuation F ((ϖ : F) ^ s * Multiplicative.toAdd Y ij.1 ij.2) < 1 :=
    fun ij => exists_pow_mul_lt_one hϖ _
  choose r hr using hent
  refine ⟨Finset.univ.sup r, ?_⟩
  rw [hx]
  have := aElt_pow_conj_upper hϖ he (Finset.univ.sup r) (Multiplicative.toAdd Y)
  simp only [ofAdd_toAdd] at this
  rw [this]
  change _ ∈ K.toSubgroup
  rw [hKJ]
  refine coarse_upper_mem_J1 he fun i j => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hr (i, j) _ (Finset.le_sup (f := r) (Finset.mem_univ (i, j)))

end CoarseContraction

end Langlands.BushnellKutzko.LevelZero
