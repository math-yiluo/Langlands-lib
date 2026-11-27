import Langlands.BaseChange.TwistedLocalDescent.Duality
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Block

/-! # The determinant of the adjoint action on the strictly block lower matrices

For `m` in the standard block Levi, `X ↦ m X m⁻¹` acts on the strictly block lower matrices
`𝔲̄(E)` with determinant `∏_{k < i} det(m_i)^{n_k} det(m_k⁻¹)^{n_i}`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear Module

universe v

variable {E : Type v} [Field E] {n : ℕ} (B : BlockShape n)

theorem coordinateBlock_index (i : Fin B.length) (s : Fin (B.size i)) :
    B.coordinateBlock (B.index i s) = i := by
  change (B.indexEquiv.symm (B.indexEquiv ⟨i, s⟩)).1 = i
  rw [Equiv.symm_apply_apply]

/-- Positions strictly below the diagonal blocks. -/
abbrev LowerPosition := {p : Fin n × Fin n // B.coordinateBlock p.2 < B.coordinateBlock p.1}

/-- Coordinates of a strictly block lower matrix. -/
def lowerLieEquiv : lowerLie (E := E) B ≃ₗ[E] (LowerPosition B → E) where
  toFun X p := X.val p.val.1 p.val.2
  invFun f := ⟨Matrix.of fun a b =>
      if h : B.coordinateBlock b < B.coordinateBlock a then f ⟨(a, b), h⟩ else 0, by
    intro a b hab
    simp [Matrix.of_apply, not_lt.mpr hab]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by
    apply Subtype.ext
    ext a b
    by_cases h : B.coordinateBlock b < B.coordinateBlock a
    · simp [h]
    · simp [h, X.property a b (not_lt.mp h)]
  right_inv f := by
    funext p
    simp [p.property]

/-- The basis of matrix units of `𝔲̄(E)`. -/
def lowerBasis : Basis (LowerPosition B) E (lowerLie (E := E) B) :=
  (Pi.basisFun E (LowerPosition B)).map (lowerLieEquiv B).symm

theorem lowerBasis_apply (q : LowerPosition B) :
    (lowerBasis (E := E) B q).val = Matrix.single q.val.1 q.val.2 1 := by
  ext a b
  simp only [lowerBasis, Basis.map_apply, Pi.basisFun_apply]
  change (if h : B.coordinateBlock b < B.coordinateBlock a then
    (Pi.single q (1 : E) : LowerPosition B → E) ⟨(a, b), h⟩ else 0) = _
  rw [Matrix.single_apply]
  split_ifs with h h' h'
  · obtain ⟨rfl, rfl⟩ := h'
    simp
  · rw [Pi.single_apply]
    split_ifs with hq
    · exfalso
      apply h'
      have := congrArg Subtype.val hq
      rw [← this]
      exact ⟨rfl, rfl⟩
    · rfl
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd q.property h
  · rfl

theorem toMatrix_lowerBasis_apply (f : Module.End E (lowerLie (E := E) B)) (p q : LowerPosition B) :
    LinearMap.toMatrix (lowerBasis B) (lowerBasis B) f p q =
      (f (lowerBasis B q)).val p.val.1 p.val.2 := by
  rw [LinearMap.toMatrix_apply]
  rfl

variable (m : B.Levi E)

/-- `X ↦ m X m⁻¹` on `𝔲̄(E)`, as an `E`-linear map. -/
def lowerAdjoint : Module.End E (lowerLie (E := E) B) :=
  (linearAdjoint (B.leviEmbedding E m)).restrict (fun _ hX => linearAdjoint_mem_lowerLie B m hX)

theorem linearAdjoint_single_apply (g : GeneralLinear n E) (a₀ b₀ a b : Fin n) :
    linearAdjoint g (Matrix.single a₀ b₀ 1) a b = g.val a a₀ * (g⁻¹).val b₀ b := by
  change ((g.val * (Matrix.single a₀ b₀ (1 : E) * (g⁻¹).val) :
    Matrix (Fin n) (Fin n) E)) a b = _
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem toMatrix_lowerAdjoint_apply (p q : LowerPosition B) :
    LinearMap.toMatrix (lowerBasis B) (lowerBasis B) (lowerAdjoint B m) p q =
      (B.leviEmbedding E m).val p.val.1 q.val.1 *
        (B.leviEmbedding E m)⁻¹.val q.val.2 p.val.2 := by
  rw [toMatrix_lowerBasis_apply]
  change linearAdjoint (B.leviEmbedding E m) (lowerBasis B q).val p.val.1 p.val.2 = _
  rw [lowerBasis_apply, linearAdjoint_single_apply]

/-- The block pair of a position, encoded as a natural number. -/
def pairCode (p : Fin B.length × Fin B.length) : ℕ := p.1.val * B.length + p.2.val

theorem pairCode_injective : Function.Injective (pairCode B) := by
  intro p q h
  simp only [pairCode] at h
  have hp := p.2.isLt
  have hq := q.2.isLt
  have hL : 0 < B.length := by omega
  have h1 : p.1.val = q.1.val := by
    have e1 : (p.1.val * B.length + p.2.val) / B.length = p.1.val := by
      rw [add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hp, zero_add]
    have e2 : (q.1.val * B.length + q.2.val) / B.length = q.1.val := by
      rw [add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hq, zero_add]
    rw [← e1, ← e2, h]
  have h2 : p.2.val = q.2.val := by
    rw [h1] at h
    omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- The block pair code of a lower position. -/
def lowerCode (p : LowerPosition B) : ℕ :=
  pairCode B (B.coordinateBlock p.val.1, B.coordinateBlock p.val.2)

theorem toMatrix_lowerAdjoint_eq_zero {p q : LowerPosition B} (h : lowerCode B p ≠ lowerCode B q) :
    LinearMap.toMatrix (lowerBasis B) (lowerBasis B) (lowerAdjoint B m) p q = 0 := by
  rw [toMatrix_lowerAdjoint_apply]
  by_cases h1 : B.coordinateBlock p.val.1 = B.coordinateBlock q.val.1
  · have h2 : B.coordinateBlock q.val.2 ≠ B.coordinateBlock p.val.2 := by
      intro h2
      apply h
      simp only [lowerCode, h1, h2]
    rw [← map_inv, leviEmbedding_apply_eq_zero B m⁻¹ h2, mul_zero]
  · rw [leviEmbedding_apply_eq_zero B m h1, zero_mul]

theorem blockTriangular_toMatrix_lowerAdjoint :
    (LinearMap.toMatrix (lowerBasis B) (lowerBasis B) (lowerAdjoint B m)).BlockTriangular
      (lowerCode B) := by
  intro p q h
  exact toMatrix_lowerAdjoint_eq_zero B m h.ne'

/-- The lower positions in a given block pair. -/
def lowerBlockEquiv (i k : Fin B.length) (hki : k < i) :
    Fin (B.size i) × Fin (B.size k) ≃
      {p : LowerPosition B // lowerCode B p = pairCode B (i, k)} := by
  refine Equiv.ofBijective (fun st => ⟨⟨(B.index i st.1, B.index k st.2), ?_⟩, ?_⟩) ⟨?_, ?_⟩
  · simpa only [coordinateBlock_index] using hki
  · simp only [lowerCode, coordinateBlock_index]
  · intro st st' h
    have h' := congrArg (fun p => p.val.val) h
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext ((B.index i).injective h'.1) ((B.index k).injective h'.2)
  · rintro ⟨⟨⟨a, b⟩, hab⟩, hc⟩
    obtain ⟨⟨i', s⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨k', t⟩, rfl⟩ := B.indexEquiv.surjective b
    have hc' := pairCode_injective B hc
    simp only [BlockShape.coordinateBlock, Equiv.symm_apply_apply, Prod.mk.injEq] at hc'
    obtain ⟨rfl, rfl⟩ := hc'
    exact ⟨(s, t), rfl⟩

theorem det_toSquareBlock_lowerAdjoint (i k : Fin B.length) (hki : k < i) :
    ((LinearMap.toMatrix (lowerBasis B) (lowerBasis B) (lowerAdjoint B m)).toSquareBlock
        (lowerCode B) (pairCode B (i, k))).det =
      (m i).val.det ^ B.size k * ((m k)⁻¹).val.det ^ B.size i := by
  rw [← Matrix.det_submatrix_equiv_self (lowerBlockEquiv B i k hki)]
  have hk : ((LinearMap.toMatrix (lowerBasis B) (lowerBasis B) (lowerAdjoint B m)).toSquareBlock
        (lowerCode B) (pairCode B (i, k))).submatrix (lowerBlockEquiv B i k hki)
        (lowerBlockEquiv B i k hki) =
      Matrix.kroneckerMap (· * ·) (m i).val ((m k)⁻¹).val.transpose := by
    ext ⟨s, t⟩ ⟨s', t'⟩
    simp only [Matrix.submatrix_apply, Matrix.toSquareBlock, Matrix.toSquareBlockProp]
    rw [Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    change LinearMap.toMatrix (lowerBasis B) (lowerBasis B) (lowerAdjoint B m)
      ⟨(B.index i s, B.index k t), _⟩ ⟨(B.index i s', B.index k t'), _⟩ = _
    rw [toMatrix_lowerAdjoint_apply, ← map_inv]
    simp only [BlockShape.leviEmbedding_apply_same, Pi.inv_apply]
  rw [hk, Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]

/-- **Determinant of `Ad(m)` on `𝔲̄(E)`.** -/
theorem det_lowerAdjoint :
    LinearMap.det (lowerAdjoint B m) =
      ∏ ik ∈ Finset.univ.filter (fun ik : Fin B.length × Fin B.length => ik.2 < ik.1),
        (m ik.1).val.det ^ B.size ik.2 * ((m ik.2)⁻¹).val.det ^ B.size ik.1 := by
  classical
  rw [← LinearMap.det_toMatrix (lowerBasis B),
    (blockTriangular_toMatrix_lowerAdjoint B m).det]
  have himage : Finset.univ.image (lowerCode B) =
      (Finset.univ.filter (fun ik : Fin B.length × Fin B.length => ik.2 < ik.1)).image
        (pairCode B) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, p.property, rfl⟩
    · rintro ⟨⟨i, k⟩, hki, rfl⟩
      have hi : 0 < B.size i := B.positive i
      have hk : 0 < B.size k := B.positive k
      exact ⟨(lowerBlockEquiv B i k hki (⟨0, hi⟩, ⟨0, hk⟩)).val,
        (lowerBlockEquiv B i k hki (⟨0, hi⟩, ⟨0, hk⟩)).property⟩
  rw [himage, Finset.prod_image (fun p _ q _ h => pairCode_injective B h)]
  apply Finset.prod_congr rfl
  rintro ⟨i, k⟩ hik
  exact det_toSquareBlock_lowerAdjoint B m i k (Finset.mem_filter.mp hik).2

end Langlands.BaseChange.TwistedLocalDescent
