import Langlands.Group.GL.PrincipalBlockFactorizationStatement
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Group

noncomputable section

open Matrix

namespace Langlands.GeneralLinear.BlockShape

universe u v w t

section Elimination

variable {R : Type v} [CommRing R] [IsLocalRing R] {α : Type w} [LinearOrder α]

/-- A matrix congruent to the identity modulo an ideal inside the maximal ideal
has a unit determinant. -/
private theorem isUnit_det_of_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Ideal R} (hJ : J ≤ IsLocalRing.maximalIdeal R) (A : Matrix ι ι R)
    (hA : ∀ x y, A x y - (1 : Matrix ι ι R) x y ∈ J) : IsUnit A.det := by
  have h1 : (Ideal.Quotient.mk J).mapMatrix A = (Ideal.Quotient.mk J).mapMatrix 1 := by
    ext x y
    exact Ideal.Quotient.eq.mpr (hA x y)
  have hd : A.det - 1 ∈ J := by
    have h2 := congrArg Matrix.det h1
    rw [← RingHom.map_det, ← RingHom.map_det, det_one] at h2
    exact Ideal.Quotient.eq.mp h2
  by_contra hu
  have hm : A.det ∈ IsLocalRing.maximalIdeal R := hu
  apply (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  rw [Ideal.eq_top_iff_one]
  simpa using (IsLocalRing.maximalIdeal R).sub_mem hm (hJ hd)

omit [IsLocalRing R] in
private theorem one_apply_subtype {ι : Type*} [DecidableEq ι] {q : ι → Prop}
    (x y : {z // q z}) :
    (1 : Matrix {z // q z} {z // q z} R) x y = (1 : Matrix ι ι R) x.val y.val := by
  by_cases h : x = y
  · subst h
    simp
  · rw [one_apply_ne h, one_apply_ne (Subtype.val_injective.ne h)]

/-- Block `LDU` elimination for matrices congruent to the identity. -/
private theorem exists_blockLDU {J : Ideal R} (hJ : J ≤ IsLocalRing.maximalIdeal R) :
    ∀ (N : ℕ) {ι : Type t} [Fintype ι] [DecidableEq ι], Fintype.card ι = N →
      ∀ (b : ι → α) (M : Matrix ι ι R), (∀ x y, M x y - (1 : Matrix ι ι R) x y ∈ J) →
      ∃ L D U : Matrix ι ι R,
        (∀ x y, (b x < b y → L x y = 0) ∧ (b x = b y → L x y = (1 : Matrix ι ι R) x y) ∧
          L x y - (1 : Matrix ι ι R) x y ∈ J) ∧
        (∀ x y, (b x ≠ b y → D x y = 0) ∧ D x y - (1 : Matrix ι ι R) x y ∈ J) ∧
        (∀ x y, (b y < b x → U x y = 0) ∧ (b x = b y → U x y = (1 : Matrix ι ι R) x y) ∧
          U x y - (1 : Matrix ι ι R) x y ∈ J) ∧
        M = L * D * U := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro ι _ _ hN b M hM
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, 1, fun x => isEmptyElim x, fun x => isEmptyElim x,
      fun x => isEmptyElim x, ?_⟩
    ext x
    exact isEmptyElim x
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min b
  let p : ι → Prop := fun x => b x = b x₀
  let e : {x // p x} ⊕ {x // ¬p x} ≃ ι := Equiv.sumCompl p
  have he_inl : ∀ x : {x // p x}, e (Sum.inl x) = x.val := fun _ => rfl
  have he_inr : ∀ x : {x // ¬p x}, e (Sum.inr x) = x.val := fun _ => rfl
  have hbp : ∀ x : {x // p x}, b x.val = b x₀ := fun x => x.property
  have hbn : ∀ x : {x // ¬p x}, b x₀ < b x.val := fun x =>
    lt_of_le_of_ne (hx₀ _) (fun h => x.property h.symm)
  have hne : ∀ (x : {x // p x}) (y : {x // ¬p x}), x.val ≠ y.val := by
    intro x y h
    apply y.property
    rw [← h]
    exact x.property
  have h1lr : ∀ (x : {x // p x}) (y : {x // ¬p x}), (1 : Matrix ι ι R) x.val y.val = 0 :=
    fun x y => one_apply_ne (hne x y)
  have h1rl : ∀ (x : {x // ¬p x}) (y : {x // p x}), (1 : Matrix ι ι R) x.val y.val = 0 :=
    fun x y => one_apply_ne (hne y x).symm
  let M' := M.submatrix e e
  let A := M'.toBlocks₁₁
  let B₁ := M'.toBlocks₁₂
  let C := M'.toBlocks₂₁
  let D₁ := M'.toBlocks₂₂
  have hA : ∀ x y, A x y - (1 : Matrix _ _ R) x y ∈ J := by
    intro x y
    rw [one_apply_subtype]
    exact hM x.val y.val
  have hB : ∀ x y, B₁ x y ∈ J := by
    intro x y
    have h := hM x.val y.val
    rw [h1lr x y, sub_zero] at h
    exact h
  have hC : ∀ x y, C x y ∈ J := by
    intro x y
    have h := hM x.val y.val
    rw [h1rl x y, sub_zero] at h
    exact h
  have hD : ∀ x y, D₁ x y - (1 : Matrix _ _ R) x y ∈ J := by
    intro x y
    rw [one_apply_subtype]
    exact hM x.val y.val
  let _ : Invertible A := invertibleOfIsUnitDet A (isUnit_det_of_congr hJ A hA)
  let S := D₁ - C * ⅟A * B₁
  have hCA : ∀ x y, (C * ⅟A) x y ∈ J := fun x y => by
    rw [mul_apply]
    exact Ideal.sum_mem _ fun z _ => J.mul_mem_right _ (hC x z)
  have hAB : ∀ x y, (⅟A * B₁) x y ∈ J := fun x y => by
    rw [mul_apply]
    exact Ideal.sum_mem _ fun z _ => J.mul_mem_left _ (hB z y)
  have hS : ∀ x y, S x y - (1 : Matrix _ _ R) x y ∈ J := by
    intro x y
    have hCAB : (C * ⅟A * B₁) x y ∈ J := by
      rw [mul_apply]
      exact Ideal.sum_mem _ fun z _ => J.mul_mem_right _ (hCA x z)
    have h := J.sub_mem (hD x y) hCAB
    simp only [S, Matrix.sub_apply]
    convert h using 1
    abel
  have hcard : Fintype.card {x // ¬p x} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (p := fun x => ¬p x) (x := x₀) (by simp [p])
  obtain ⟨L₂, D₂, U₂, hL₂, hD₂, hU₂, hS₂⟩ :=
    ih _ hcard rfl (fun x => b x.val) S hS
  have hM' : M' = fromBlocks A B₁ C D₁ := (fromBlocks_toBlocks M').symm
  have hfac : fromBlocks A B₁ C D₁ =
      fromBlocks 1 0 (C * ⅟A) L₂ * fromBlocks A 0 0 D₂ * fromBlocks 1 (⅟A * B₁) 0 U₂ := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, Matrix.invOf_mul_cancel_right, Matrix.mul_invOf_cancel_left, ← hS₂]
    congr 1
    simp only [S, Matrix.mul_assoc]
    abel
  have hMM : M = M'.submatrix e.symm e.symm := by
    ext x y
    simp [M']
  refine ⟨(fromBlocks 1 0 (C * ⅟A) L₂).submatrix e.symm e.symm,
    (fromBlocks A 0 0 D₂).submatrix e.symm e.symm,
    (fromBlocks 1 (⅟A * B₁) 0 U₂).submatrix e.symm e.symm, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    rw [submatrix_apply, e.symm_apply_apply, e.symm_apply_apply]
    rcases u with u | u <;> rcases v with v | v
    · rw [fromBlocks_apply₁₁, he_inl, he_inl, one_apply_subtype, hbp u, hbp v]
      exact ⟨fun h => absurd h (lt_irrefl _), fun _ => rfl, by simp⟩
    · rw [fromBlocks_apply₁₂, he_inl, he_inr, h1lr u v]
      exact ⟨fun _ => rfl, fun _ => rfl, by simp⟩
    · rw [fromBlocks_apply₂₁, he_inr, he_inl, h1rl u v, hbp v]
      exact ⟨fun h => absurd h (not_lt.mpr (hbn u).le), fun h => absurd h (hbn u).ne',
        by simpa using hCA u v⟩
    · rw [fromBlocks_apply₂₂, he_inr, he_inr]
      have h := hL₂ u v
      rw [one_apply_subtype] at h
      exact h
  · intro x y
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    rw [submatrix_apply, e.symm_apply_apply, e.symm_apply_apply]
    rcases u with u | u <;> rcases v with v | v
    · rw [fromBlocks_apply₁₁, he_inl, he_inl, hbp u, hbp v]
      exact ⟨fun h => absurd rfl h, hM u.val v.val⟩
    · rw [fromBlocks_apply₁₂, he_inl, he_inr, h1lr u v]
      exact ⟨fun _ => rfl, by simp⟩
    · rw [fromBlocks_apply₂₁, he_inr, he_inl, h1rl u v]
      exact ⟨fun _ => rfl, by simp⟩
    · rw [fromBlocks_apply₂₂, he_inr, he_inr]
      have h := hD₂ u v
      rw [one_apply_subtype] at h
      exact h
  · intro x y
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    rw [submatrix_apply, e.symm_apply_apply, e.symm_apply_apply]
    rcases u with u | u <;> rcases v with v | v
    · rw [fromBlocks_apply₁₁, he_inl, he_inl, one_apply_subtype, hbp u, hbp v]
      exact ⟨fun h => absurd h (lt_irrefl _), fun _ => rfl, by simp⟩
    · rw [fromBlocks_apply₁₂, he_inl, he_inr, h1lr u v, hbp u]
      exact ⟨fun h => absurd h (not_lt.mpr (hbn v).le), fun h => absurd h (hbn v).ne,
        by simpa using hAB u v⟩
    · rw [fromBlocks_apply₂₁, he_inr, he_inl, h1rl u v]
      exact ⟨fun _ => rfl, fun _ => rfl, by simp⟩
    · rw [fromBlocks_apply₂₂, he_inr, he_inr]
      have h := hU₂ u v
      rw [one_apply_subtype] at h
      exact h
  · rw [submatrix_mul_equiv, submatrix_mul_equiv, ← hfac, ← hM']
    exact hMM

end Elimination

section Blocks

variable {n : ℕ} (B : GeneralLinear.BlockShape n) (R : Type v) [CommRing R]

private theorem indexEquiv_symm_index (i : Fin B.length) (r : Fin (B.size i)) :
    B.indexEquiv.symm (B.index i r) = ⟨i, r⟩ :=
  B.indexEquiv.symm_apply_apply ⟨i, r⟩

private theorem index_ne {i j : Fin B.length} (r : Fin (B.size i)) (s : Fin (B.size j))
    (hij : i ≠ j) : B.index i r ≠ B.index j s := by
  intro h
  have h' : B.indexEquiv ⟨i, r⟩ = B.indexEquiv ⟨j, s⟩ := h
  exact hij (congrArg Sigma.fst (B.indexEquiv.injective h'))

private theorem one_index_ne {i j : Fin B.length} (r : Fin (B.size i))
    (s : Fin (B.size j)) (hij : i ≠ j) :
    (1 : GeneralLinear n R) (B.index i r) (B.index j s) = 0 := by
  change (1 : Matrix (Fin n) (Fin n) R) (B.index i r) (B.index j s) = 0
  exact one_apply_ne (B.index_ne r s hij)

private theorem one_index_same (i : Fin B.length) (r s : Fin (B.size i)) :
    (1 : GeneralLinear n R) (B.index i r) (B.index i s) = if r = s then 1 else 0 := by
  change (1 : Matrix (Fin n) (Fin n) R) (B.index i r) (B.index i s) = _
  simp only [one_apply, (B.index i).injective.eq_iff]

/-- Two matrices agreeing on every pair of block coordinates are equal. -/
private theorem ext_index {g h : GeneralLinear n R}
    (H : ∀ (i j : Fin B.length) (r : Fin (B.size i)) (s : Fin (B.size j)),
      g (B.index i r) (B.index j s) = h (B.index i r) (B.index j s)) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  exact H i j r s

/-- The opposite radical meets the upper parabolic trivially. -/
private theorem eq_one_of_mem_opposite_of_mem_parabolic {g : GeneralLinear n R}
    (hl : g ∈ B.oppositeUnipotentSubgroup R) (hp : g ∈ B.parabolic R) : g = 1 := by
  rw [mem_oppositeUnipotentSubgroup_iff, mem_oppositeParabolic_iff] at hl
  rw [mem_parabolic_iff] at hp
  apply B.ext_index R
  intro i j r s
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hl.1 i j r s hij, B.one_index_ne R r s hij.ne]
  · rw [hl.2 i r s, B.one_index_same R]
  · rw [hp i j r s hij, B.one_index_ne R r s hij.ne']

/-- The common Levi meets the upper radical trivially. -/
private theorem eq_one_of_mem_levi_of_mem_unipotent {g : GeneralLinear n R}
    (hm : g ∈ B.leviSubgroup R) (hu : g ∈ B.unipotentSubgroup R) : g = 1 := by
  obtain ⟨m, rfl⟩ := hm
  rw [mem_unipotentSubgroup_iff] at hu
  apply B.ext_index R
  intro i j r s
  by_cases hij : i = j
  · subst hij
    rw [hu.2 i r s, B.one_index_same R]
  · rw [B.leviEmbedding_apply_ne R m r s hij, B.one_index_ne R r s hij]

private theorem leviSubgroup_le_parabolic : B.leviSubgroup R ≤ B.parabolic R := by
  rintro _ ⟨m, rfl⟩
  exact (B.leviInParabolic R m).property

private theorem unipotentSubgroup_le_parabolic : B.unipotentSubgroup R ≤ B.parabolic R :=
  fun g hg => ((B.mem_unipotentSubgroup_iff R g).1 hg).1

/-- A block diagonal invertible matrix lies in the common Levi. -/
private theorem mem_leviSubgroup_of_entries {g : GeneralLinear n R}
    (hg : ∀ x y : Fin n, (B.indexEquiv.symm x).1 ≠ (B.indexEquiv.symm y).1 → g x y = 0) :
    g ∈ B.leviSubgroup R := by
  have hg' : ∀ (i j : Fin B.length) (r : Fin (B.size i)) (s : Fin (B.size j)), i ≠ j →
      g (B.index i r) (B.index j s) = 0 := fun i j r s hij =>
    hg _ _ (by rwa [B.indexEquiv_symm_index, B.indexEquiv_symm_index])
  have hp : g ∈ B.parabolic R :=
    (B.mem_parabolic_iff R g).2 fun i j r s hij => hg' i j r s hij.ne'
  refine ⟨B.leviProjection R ⟨g, hp⟩, ?_⟩
  apply B.ext_index R
  intro i j r s
  by_cases hij : i = j
  · subst hij
    rw [B.leviEmbedding_apply_same R, leviProjection_apply]
  · rw [B.leviEmbedding_apply_ne R _ r s hij, hg' i j r s hij]

/-- Lower block triangular entries with identity diagonal blocks give the opposite radical. -/
private theorem mem_oppositeUnipotentSubgroup_of_entries {g : GeneralLinear n R}
    (h₁ : ∀ x y : Fin n, (B.indexEquiv.symm x).1 < (B.indexEquiv.symm y).1 → g x y = 0)
    (h₂ : ∀ x y : Fin n, (B.indexEquiv.symm x).1 = (B.indexEquiv.symm y).1 →
      g x y = (1 : Matrix (Fin n) (Fin n) R) x y) :
    g ∈ B.oppositeUnipotentSubgroup R := by
  rw [mem_oppositeUnipotentSubgroup_iff, mem_oppositeParabolic_iff]
  refine ⟨fun i j r s hij => h₁ _ _ ?_, fun i r s => ?_⟩
  · rwa [B.indexEquiv_symm_index, B.indexEquiv_symm_index]
  · rw [h₂ _ _ (by rw [B.indexEquiv_symm_index, B.indexEquiv_symm_index])]
    exact B.one_index_same R i r s

/-- Upper block triangular entries with identity diagonal blocks give the upper radical. -/
private theorem mem_unipotentSubgroup_of_entries {g : GeneralLinear n R}
    (h₁ : ∀ x y : Fin n, (B.indexEquiv.symm y).1 < (B.indexEquiv.symm x).1 → g x y = 0)
    (h₂ : ∀ x y : Fin n, (B.indexEquiv.symm x).1 = (B.indexEquiv.symm y).1 →
      g x y = (1 : Matrix (Fin n) (Fin n) R) x y) :
    g ∈ B.unipotentSubgroup R := by
  rw [mem_unipotentSubgroup_iff, mem_parabolic_iff]
  refine ⟨fun i j r s hij => h₁ _ _ ?_, fun i r s => ?_⟩
  · rwa [B.indexEquiv_symm_index, B.indexEquiv_symm_index]
  · rw [h₂ _ _ (by rw [B.indexEquiv_symm_index, B.indexEquiv_symm_index])]
    exact B.one_index_same R i r s

/-- Ordered opposite-radical, common-Levi and upper-radical factors are unique
in any subgroup. -/
theorem iwahoriProduct_injective (K : Subgroup (GeneralLinear n R)) :
    Function.Injective (B.iwahoriProduct R K) := by
  rintro ⟨l₁, m₁, u₁⟩ ⟨l₂, m₂, u₂⟩ h
  have h' : l₁.val * m₁.val * u₁.val = l₂.val * m₂.val * u₂.val := congrArg Subtype.val h
  have hl : l₂.val⁻¹ * l₁.val = m₂.val * u₂.val * u₁.val⁻¹ * m₁.val⁻¹ := by
    calc l₂.val⁻¹ * l₁.val
        = l₂.val⁻¹ * (l₁.val * m₁.val * u₁.val) * u₁.val⁻¹ * m₁.val⁻¹ := by group
      _ = l₂.val⁻¹ * (l₂.val * m₂.val * u₂.val) * u₁.val⁻¹ * m₁.val⁻¹ := by rw [h']
      _ = m₂.val * u₂.val * u₁.val⁻¹ * m₁.val⁻¹ := by group
  have hl1 : l₂.val⁻¹ * l₁.val = 1 := by
    apply B.eq_one_of_mem_opposite_of_mem_parabolic R
    · exact (B.oppositeUnipotentSubgroup R).mul_mem
        ((B.oppositeUnipotentSubgroup R).inv_mem l₂.property.2) l₁.property.2
    · rw [hl]
      have hm₁ := B.leviSubgroup_le_parabolic R m₁.property.2
      have hm₂ := B.leviSubgroup_le_parabolic R m₂.property.2
      have hu₁ := B.unipotentSubgroup_le_parabolic R u₁.property.2
      have hu₂ := B.unipotentSubgroup_le_parabolic R u₂.property.2
      exact (B.parabolic R).mul_mem ((B.parabolic R).mul_mem
        ((B.parabolic R).mul_mem hm₂ hu₂) ((B.parabolic R).inv_mem hu₁))
        ((B.parabolic R).inv_mem hm₁)
  have hl' : l₁.val = l₂.val := (inv_mul_eq_one.mp hl1).symm
  have hmu : m₁.val * u₁.val = m₂.val * u₂.val := by
    rw [hl', mul_assoc, mul_assoc] at h'
    exact mul_left_cancel h'
  have hm : m₂.val⁻¹ * m₁.val = u₂.val * u₁.val⁻¹ := by
    calc m₂.val⁻¹ * m₁.val = m₂.val⁻¹ * (m₁.val * u₁.val) * u₁.val⁻¹ := by group
      _ = m₂.val⁻¹ * (m₂.val * u₂.val) * u₁.val⁻¹ := by rw [hmu]
      _ = u₂.val * u₁.val⁻¹ := by group
  have hm1 : m₂.val⁻¹ * m₁.val = 1 := by
    apply B.eq_one_of_mem_levi_of_mem_unipotent R
    · exact (B.leviSubgroup R).mul_mem ((B.leviSubgroup R).inv_mem m₂.property.2)
        m₁.property.2
    · rw [hm]
      exact (B.unipotentSubgroup R).mul_mem u₂.property.2
        ((B.unipotentSubgroup R).inv_mem u₁.property.2)
  have hm' : m₁.val = m₂.val := (inv_mul_eq_one.mp hm1).symm
  have hu' : u₁.val = u₂.val := by
    rw [hm'] at hmu
    exact mul_left_cancel hmu
  exact Prod.ext (Subtype.ext hl') (Prod.ext (Subtype.ext hm') (Subtype.ext hu'))

end Blocks

section Principal

private theorem ringHom_one_apply {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    {ι : Type*} [DecidableEq ι] (x y : ι) :
    f ((1 : Matrix ι ι S) x y) = (1 : Matrix ι ι T) x y := by
  by_cases h : x = y
  · subst h
    simp
  · simp [one_apply_ne h]

/-- Every positive principal level subgroup is the ordered product of its
opposite-radical, common-Levi and upper-radical parts. -/
theorem principalLevelSubgroup_iwahoriProduct_surjective (k : Type u) [Field k]
    [ValuativeRel k] (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)) (a : ℕ) (ha : 0 < a) :
    Function.Surjective
      (B.iwahoriProduct k (Langlands.Conductor.principalLevelSubgroup k n a)) := by
  let O := (ValuativeRel.valuation k).integer
  let I : Ideal O := IsLocalRing.maximalIdeal O ^ a
  let f : O →+* k := O.subtype
  have hI : I ≤ IsLocalRing.maximalIdeal O := Ideal.pow_le_self ha.ne'
  rintro ⟨x, hx⟩
  have hx' : x ∈ (Langlands.Conductor.integralPrincipalCongruence n I).map
      (Matrix.GeneralLinearGroup.map f) := hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx'
  rw [Langlands.Conductor.mem_integralPrincipalCongruence] at hg
  obtain ⟨L, D, U, hL, hD, hU, hLDU⟩ :=
    exists_blockLDU (ι := Fin (n + 1)) hI _ rfl (fun x => (B.indexEquiv.symm x).1)
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) O) hg
  let l : GL (Fin (n + 1)) O :=
    Matrix.GeneralLinearGroup.mk'' L (isUnit_det_of_congr hI L fun x y => (hL x y).2.2)
  let d : GL (Fin (n + 1)) O :=
    Matrix.GeneralLinearGroup.mk'' D (isUnit_det_of_congr hI D fun x y => (hD x y).2)
  let u : GL (Fin (n + 1)) O :=
    Matrix.GeneralLinearGroup.mk'' U (isUnit_det_of_congr hI U fun x y => (hU x y).2.2)
  have hgl : g = l * d * u := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hLDU
  have hK : ∀ h : GL (Fin (n + 1)) O, (∀ x y, h x y -
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) O) x y ∈ I) →
      Matrix.GeneralLinearGroup.map f h ∈ Langlands.Conductor.principalLevelSubgroup k n a :=
    fun h hh => (Langlands.Conductor.map_mem_principalCongruenceSubgroup O n I h).2
      ((Langlands.Conductor.mem_integralPrincipalCongruence n I h).2 hh)
  have hl : Matrix.GeneralLinearGroup.map f l ∈ B.oppositeUnipotentSubgroup k := by
    apply B.mem_oppositeUnipotentSubgroup_of_entries k
    · intro x y hxy
      rw [Matrix.GeneralLinearGroup.map_apply, show l x y = L x y from rfl,
        (hL x y).1 hxy, map_zero]
    · intro x y hxy
      rw [Matrix.GeneralLinearGroup.map_apply, show l x y = L x y from rfl,
        (hL x y).2.1 hxy, ringHom_one_apply]
  have hd : Matrix.GeneralLinearGroup.map f d ∈ B.leviSubgroup k := by
    apply B.mem_leviSubgroup_of_entries k
    intro x y hxy
    rw [Matrix.GeneralLinearGroup.map_apply, show d x y = D x y from rfl,
      (hD x y).1 hxy, map_zero]
  have hu : Matrix.GeneralLinearGroup.map f u ∈ B.unipotentSubgroup k := by
    apply B.mem_unipotentSubgroup_of_entries k
    · intro x y hxy
      rw [Matrix.GeneralLinearGroup.map_apply, show u x y = U x y from rfl,
        (hU x y).1 hxy, map_zero]
    · intro x y hxy
      rw [Matrix.GeneralLinearGroup.map_apply, show u x y = U x y from rfl,
        (hU x y).2.1 hxy, ringHom_one_apply]
  refine ⟨(⟨Matrix.GeneralLinearGroup.map f l,
      (B.mem_iwahoriLower k _ _).2 ⟨hK l fun x y => (hL x y).2.2, hl⟩⟩,
    ⟨Matrix.GeneralLinearGroup.map f d,
      (B.mem_iwahoriLevi k _ _).2 ⟨hK d fun x y => (hD x y).2, hd⟩⟩,
    ⟨Matrix.GeneralLinearGroup.map f u,
      (B.mem_iwahoriUpper k _ _).2 ⟨hK u fun x y => (hU x y).2.2, hu⟩⟩), ?_⟩
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.map f l * Matrix.GeneralLinearGroup.map f d *
    Matrix.GeneralLinearGroup.map f u = Matrix.GeneralLinearGroup.map f g
  rw [hgl, map_mul, map_mul]

/-- Positive principal level subgroups have unique ordered block Iwahori factorizations,
over any field with a valuative relation. -/
theorem principalLevelSubgroup_iwahoriProduct_bijective (k : Type u) [Field k]
    [ValuativeRel k] (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)) (a : ℕ) (ha : 0 < a) :
    Function.Bijective
      (B.iwahoriProduct k (Langlands.Conductor.principalLevelSubgroup k n a)) :=
  ⟨B.iwahoriProduct_injective k _,
    principalLevelSubgroup_iwahoriProduct_surjective k n B a ha⟩

/-- The positive principal congruence block factorization statement. -/
theorem principalBlockFactorization : PrincipalBlockFactorizationStatement.{u} := by
  intro k _ _ _ _ n B a ha
  exact principalLevelSubgroup_iwahoriProduct_bijective k n B a ha

end Principal

end Langlands.GeneralLinear.BlockShape
