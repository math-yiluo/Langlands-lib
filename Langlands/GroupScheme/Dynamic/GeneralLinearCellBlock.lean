import Langlands.GroupScheme.Dynamic.GeneralLinear

/-! # A block lemma for the opposite cell of `GL_n`

Let `a : ι → ℤ` be weights and `I ⊆ ι` a set of indices. If `H = V Q` with `V` block unipotent
for `-a` and `Q` block parabolic for `a`, and `H` has no entries from the `I`-columns to the
complementary rows, then neither has `Q`. Block Levi matrices normalize both block subgroups.
-/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.GeneralLinear

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type*} [CommRing A] (a : ι → ℤ)

section BlockLemma

variable (p : ι → Prop) [DecidablePred p]

omit [DecidableEq ι] in
/-- Columns `I` of a product `X H` only see the block `H_{II}` when `H_{I'I} = 0`. -/
theorem submatrix_mul_of_compl_zero {κ : Type*} (f : κ → ι) {X H : Matrix ι ι A}
    (hH : ∀ r s, ¬ p r → p s → H r s = 0) :
    (X * H).submatrix f (Subtype.val : {i // p i} → ι) =
      X.submatrix f (Subtype.val : {i // p i} → ι) *
        H.submatrix (Subtype.val : {i // p i} → ι) (Subtype.val : {i // p i} → ι) := by
  ext r s
  simp only [submatrix_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have h0 : ∑ t : {i // ¬ p i}, X (f r) t * H t s = 0 :=
    Finset.sum_eq_zero fun t _ => by rw [hH t s t.2 s.2, mul_zero]
  rw [h0, add_zero]

/-- **The block lemma.** Let `V'` have the entries of the identity at all `(i, j)` with
`a j ≤ a i` (the inverse of a block unipotent matrix for `-a`), let `Q` vanish at all `(i, j)`
with `a i < a j` (block parabolic for `a`), and let `Q = V' H` for an invertible `H` with
`H_{rs} = 0` whenever `r ∉ I` and `s ∈ I`. Then `Q_{rs} = 0` whenever `r ∉ I` and `s ∈ I`. -/
theorem eq_zero_of_mul_of_compl_zero {V' Q H Hinv : Matrix ι ι A}
    (hV' : ∀ i j, a j ≤ a i → V' i j = (1 : Matrix ι ι A) i j)
    (hQ : ∀ i j, a i < a j → Q i j = 0) (hQV : Q = V' * H) (hinv : Hinv * H = 1)
    (hH : ∀ r s, ¬ p r → p s → H r s = 0) :
    ∀ r s, ¬ p r → p s → Q r s = 0 := by
  -- the blocks of the relevant matrices
  set H₁ : Matrix {i // p i} {i // p i} A := H.submatrix Subtype.val Subtype.val with hH₁
  set V₁ : Matrix {i // p i} {i // p i} A := V'.submatrix Subtype.val Subtype.val with hV₁
  set V₂ : Matrix {i // ¬ p i} {i // p i} A := V'.submatrix Subtype.val Subtype.val with hV₂
  set Q₁ : Matrix {i // p i} {i // p i} A := Q.submatrix Subtype.val Subtype.val with hQ₁
  set Q₂ : Matrix {i // ¬ p i} {i // p i} A := Q.submatrix Subtype.val Subtype.val with hQ₂
  have hQ₁V : Q₁ = V₁ * H₁ := by
    rw [hQ₁, hQV]
    exact submatrix_mul_of_compl_zero p _ hH
  have hQ₂V : Q₂ = V₂ * H₁ := by
    rw [hQ₂, hQV]
    exact submatrix_mul_of_compl_zero p _ hH
  have hH₁ : IsUnit H₁.det := by
    refine isUnit_det_of_left_inverse (B := Hinv.submatrix Subtype.val Subtype.val) ?_
    rw [← submatrix_mul_of_compl_zero p _ hH, hinv]
    exact submatrix_one _ Subtype.val_injective
  -- `V₁` is block triangular with identity diagonal blocks
  have hV₁T : V₁.BlockTriangular (a ∘ Subtype.val) := fun i j hij => by
    change V' i.1 j.1 = 0
    rw [hV' i.1 j.1 hij.le]
    exact one_apply_ne fun h => by
      have h' : a j.1 < a i.1 := hij
      rw [h] at h'
      exact lt_irrefl _ h'
  have hV₁det : V₁.det = 1 := by
    rw [hV₁T.det]
    refine Finset.prod_eq_one fun c _ => ?_
    have h1 : V₁.toSquareBlock (a ∘ Subtype.val) c = 1 := by
      ext i j
      rw [toSquareBlock_def, of_apply]
      change V' i.1.1 j.1.1 = _
      have hij : a j.1.1 = a i.1.1 := by
        have hi := i.2
        have hj := j.2
        simp only [Function.comp_apply] at hi hj
        rw [hi, hj]
      rw [hV' _ _ hij.le]
      by_cases h : i = j
      · subst h
        simp
      · rw [one_apply_ne fun h' => h (Subtype.ext (Subtype.ext h')), one_apply_ne h]
    rw [h1, det_one]
  have hV₁u : IsUnit V₁.det := by rw [hV₁det]; exact isUnit_one
  have hQ₁u : IsUnit Q₁.det := by rw [hQ₁V, det_mul]; exact hV₁u.mul hH₁
  -- `Q₁` is block triangular for the reversed weights
  have hQ₁T : Q₁.BlockTriangular (OrderDual.toDual ∘ a ∘ Subtype.val) := fun i j hij =>
    hQ i.1 j.1 hij
  -- the two expressions of `E = Q₂ Q₁⁻¹`
  have hE : Q₂ * Q₁⁻¹ = V₂ * V₁⁻¹ := by
    rw [hQ₂V, hQ₁V, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc H₁,
      mul_nonsing_inv _ hH₁, Matrix.one_mul]
  have hV₁iT : V₁⁻¹.BlockTriangular (a ∘ Subtype.val) := by
    let := V₁.invertibleOfIsUnitDet hV₁u
    exact blockTriangular_inv_of_blockTriangular hV₁T
  have hQ₁iT : Q₁⁻¹.BlockTriangular (OrderDual.toDual ∘ a ∘ Subtype.val) := by
    let := Q₁.invertibleOfIsUnitDet hQ₁u
    exact blockTriangular_inv_of_blockTriangular hQ₁T
  have hE0 : Q₂ * Q₁⁻¹ = 0 := by
    ext r s
    rw [Matrix.zero_apply]
    rcases le_or_gt (a s.1) (a r.1) with hrs | hrs
    · rw [hE, mul_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      rcases le_or_gt (a t.1) (a r.1) with htr | htr
      · change V' r.1 t.1 * _ = 0
        rw [hV' r.1 t.1 htr, one_apply_ne fun h : (r.1 : ι) = t.1 => r.2 (h ▸ t.2), zero_mul]
      · rw [hV₁iT (show a s.1 < a t.1 from lt_of_le_of_lt hrs htr), mul_zero]
    · rw [mul_apply]
      refine Finset.sum_eq_zero fun t _ => ?_
      rcases le_or_gt (a t.1) (a r.1) with htr | htr
      · rw [hQ₁iT (OrderDual.toDual_lt_toDual.2 (lt_of_le_of_lt htr hrs)), mul_zero]
      · change Q r.1 t.1 * _ = 0
        rw [hQ r.1 t.1 htr, zero_mul]
  have hQ₂0 : Q₂ = 0 := by
    rw [← Matrix.mul_one Q₂, ← nonsing_inv_mul _ hQ₁u, ← Matrix.mul_assoc, hE0, Matrix.zero_mul]
  intro r s hr hs
  have := congrFun (congrFun hQ₂0 ⟨r, hr⟩) ⟨s, hs⟩
  exact this

end BlockLemma

section Conjugation

variable (A)

theorem blockLeviSubgroup_neg : blockLeviSubgroup A (-a) = blockLeviSubgroup A a := by
  ext g
  simp only [mem_blockLeviSubgroup, Pi.neg_apply, ne_eq, neg_inj]

theorem blockLeviSubgroup_le_blockParabolicSubgroup :
    blockLeviSubgroup A a ≤ blockParabolicSubgroup A a := fun _ hg =>
  (mem_blockParabolicSubgroup A a).2 fun i j hij => hg i j hij.ne

variable {A}

/-- Block unipotent matrices are block parabolic. -/
theorem blockUnipotentSubgroup_le_blockParabolicSubgroup :
    blockUnipotentSubgroup A a ≤ blockParabolicSubgroup A a := fun _ hg =>
  ((blockUnipotent_iff A a _).1 hg).1

/-- Block Levi matrices normalize the block unipotent subgroup. -/
theorem conj_mem_blockUnipotentSubgroup {L V : GL ι A} (hL : L ∈ blockLeviSubgroup A a)
    (hV : V ∈ blockUnipotentSubgroup A a) : L⁻¹ * V * L ∈ blockUnipotentSubgroup A a := by
  have hLP := blockLeviSubgroup_le_blockParabolicSubgroup A a hL
  have hLiP := (blockParabolicSubgroup A a).inv_mem hLP
  have hVP := blockUnipotentSubgroup_le_blockParabolicSubgroup a hV
  obtain ⟨-, hVD⟩ := (blockUnipotent_iff A a _).1 hV
  refine (blockUnipotent_iff A a _).2
    ⟨(blockParabolicSubgroup A a).mul_mem ((blockParabolicSubgroup A a).mul_mem hLiP hVP) hLP, ?_⟩
  rw [Units.val_mul, Units.val_mul,
    blockDiagonalPart_mul A a (Matrix.BlockTriangular.mul hLiP hVP) hLP,
    blockDiagonalPart_mul A a hLiP hVP, hVD, Matrix.mul_one,
    ← blockDiagonalPart_mul A a hLiP hLP, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    blockDiagonalPart_one]

/-- Block Levi matrices normalize the block parabolic subgroup. -/
theorem conj_mem_blockParabolicSubgroup {L Q : GL ι A} (hL : L ∈ blockLeviSubgroup A a)
    (hQ : Q ∈ blockParabolicSubgroup A a) : L⁻¹ * Q * L ∈ blockParabolicSubgroup A a := by
  have hLP := blockLeviSubgroup_le_blockParabolicSubgroup A a hL
  exact (blockParabolicSubgroup A a).mul_mem
    ((blockParabolicSubgroup A a).mul_mem ((blockParabolicSubgroup A a).inv_mem hLP) hQ) hLP

end Conjugation

/-- **The block lemma for invertible matrices.** If `H = V Q` with `V` block unipotent for `-a`
and `Q` block parabolic for `a`, and `H_{rs} = 0` whenever `r ∉ I` and `s ∈ I`, then
`Q_{rs} = 0` whenever `r ∉ I` and `s ∈ I`. -/
theorem eq_zero_of_eq_mul_of_compl_zero (p : ι → Prop) [DecidablePred p] {H V Q : GL ι A}
    (hV : V ∈ blockUnipotentSubgroup A (-a)) (hQ : Q ∈ blockParabolicSubgroup A a)
    (hHVQ : H = V * Q) (hH : ∀ r s, ¬ p r → p s → (H : Matrix ι ι A) r s = 0) :
    ∀ r s, ¬ p r → p s → (Q : Matrix ι ι A) r s = 0 := by
  have hV' := (blockUnipotentSubgroup A (-a)).inv_mem hV
  refine eq_zero_of_mul_of_compl_zero a p (V' := ((V⁻¹ : GL ι A) : Matrix ι ι A))
    (Hinv := ((H⁻¹ : GL ι A) : Matrix ι ι A))
    (fun i j hij => hV' i j (by simp only [Pi.neg_apply]; omega))
    (fun i j hij => (mem_blockParabolicSubgroup A a).1 hQ i j hij) ?_ ?_ hH
  · rw [hHVQ, ← Units.val_mul, inv_mul_cancel_left]
  · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

end Langlands.GroupScheme.GeneralLinear
