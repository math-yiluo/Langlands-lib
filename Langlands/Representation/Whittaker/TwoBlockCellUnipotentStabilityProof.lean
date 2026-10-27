import Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityStatement
import Langlands.Representation.Shahidi.TwoBlocks
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Instances.Matrix

/-!
# Proof of the upper unipotent stability of the two-block cell submodule

Read through the rank exchange `GL_(A+B) ≅ GL_(B+A)`, an upper unipotent `u`
lies in the standard parabolic of shape `(B, A)`, with diagonal blocks `α`, `δ`
and upper-right block `β`. Then `w n(x) u = diag(δ, α) w n(y)` with
`y = α⁻¹ (β + x δ)`. So right translation by `u` preserves the cell, and the
restriction of `ξ(u) f` is `ρ(diag(δ, α))` applied to the restriction of `f`
composed with the affine homeomorphism `x ↦ α⁻¹ (β + x δ)`.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear

universe uF uV u

section Matrix

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (R : Type u) [CommRing R]

private theorem mul_apply_add (P Q : Langlands.GeneralLinear (n + m) R) (i j : Fin (n + m)) :
    (P * Q) i j = ∑ k : Fin n, P i (k.castAdd m) * Q (k.castAdd m) j +
      ∑ k : Fin m, P i (k.natAdd n) * Q (k.natAdd n) j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]

/-- The diagonal blocks `(α, δ)` of an element of the parabolic of shape `(n, m)`. -/
def parabolicDiagonal (g : (Shahidi.twoBlocks n m hn hm).parabolic R) :
    Langlands.GeneralLinear n R × Langlands.GeneralLinear m R :=
  Shahidi.twoBlockLeviEquiv hn hm R ((Shahidi.twoBlocks n m hn hm).leviProjection R g)

theorem parabolicDiagonal_fst_apply (g : (Shahidi.twoBlocks n m hn hm).parabolic R)
    (i j : Fin n) :
    (parabolicDiagonal hm hn R g).1 i j = g.val (i.castAdd m) (j.castAdd m) :=
  Shahidi.twoBlocks_leviProjection_first hn hm R g i j

theorem parabolicDiagonal_snd_apply (g : (Shahidi.twoBlocks n m hn hm).parabolic R)
    (i j : Fin m) :
    (parabolicDiagonal hm hn R g).2 i j = g.val (i.natAdd n) (j.natAdd n) :=
  Shahidi.twoBlocks_leviProjection_second hn hm R g i j

/-- The upper-right block `β` of a matrix of total rank `n + m`. -/
def parabolicCorner (g : Langlands.GeneralLinear (n + m) R) : Matrix (Fin n) (Fin m) R :=
  fun i j => g (i.castAdd m) (j.natAdd n)

/-- The affine change of coordinates `x ↦ α⁻¹ (β + x δ)` attached to `g`. -/
def parabolicShift (g : (Shahidi.twoBlocks n m hn hm).parabolic R)
    (x : Matrix (Fin n) (Fin m) R) : Matrix (Fin n) (Fin m) R :=
  (↑(parabolicDiagonal hm hn R g).1⁻¹ : Matrix (Fin n) (Fin n) R) *
    (parabolicCorner R g.val + x * (↑(parabolicDiagonal hm hn R g).2 : Matrix (Fin m) (Fin m) R))

/-- Block factorization `[[1, x], [0, 1]] g = diag(α, δ) [[1, y], [0, 1]]` for `g` in
the parabolic of shape `(n, m)`, with `y = α⁻¹ (β + x δ)`. -/
theorem upper_mul_parabolic (x : Matrix (Fin n) (Fin m) R)
    (g : (Shahidi.twoBlocks n m hn hm).parabolic R) :
    Shahidi.upper n m R x * g.val =
      blockSum ((parabolicDiagonal hm hn R g).1, (parabolicDiagonal hm hn R g).2) *
        Shahidi.upper n m R (parabolicShift hm hn R g x) := by
  have hz : ∀ (i : Fin m) (j : Fin n), g.val (i.natAdd n) (j.castAdd m) = 0 :=
    (Shahidi.twoBlocks_mem_parabolic_iff hn hm R g.val).mp g.property
  have hshift : (↑(parabolicDiagonal hm hn R g).1 : Matrix (Fin n) (Fin n) R) *
      parabolicShift hm hn R g x =
        parabolicCorner R g.val +
          x * (↑(parabolicDiagonal hm hn R g).2 : Matrix (Fin m) (Fin m) R) := by
    rw [parabolicShift, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  apply Units.ext
  ext i j
  rw [mul_apply_add, mul_apply_add]
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rename_i i j
    simp [hz, parabolicDiagonal_fst_apply, -Prod.mk.eta]
  · rename_i i j
    have h := congrFun (congrFun hshift i) j
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.mul_apply] at h
    simp only [Shahidi.upper_first_first, Shahidi.upper_first_second,
      Shahidi.upper_second_second, blockSum_apply_left, blockSum_apply_left_right,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const_zero, add_zero]
    rw [h]
    simp only [parabolicCorner, parabolicDiagonal_snd_apply]
  · rename_i i j
    simp [hz, -Prod.mk.eta]
  · rename_i i j
    simp [parabolicDiagonal_snd_apply, -Prod.mk.eta]

/-- With `w` the block Weyl element and `n(x)` the exchanged radical,
`w n(x) g' = diag(δ, α) w n(y)` for `g'` the rank exchange of a parabolic `g`. -/
theorem blockWeyl_mul_intertwiningUnipotent_mul_swapRank (x : Matrix (Fin n) (Fin m) R)
    (g : (Shahidi.twoBlocks n m hn hm).parabolic R) :
    Shahidi.blockWeyl m n R * Shahidi.intertwiningUnipotent m n R x *
        Shahidi.swapRank m n R g.val =
      blockSum ((parabolicDiagonal hm hn R g).2, (parabolicDiagonal hm hn R g).1) *
        (Shahidi.blockWeyl m n R *
          Shahidi.intertwiningUnipotent m n R (parabolicShift hm hn R g x)) := by
  have h1 : Shahidi.swapRank m n R (Shahidi.upper n m R x) * Shahidi.swapRank m n R g.val =
      Shahidi.swapRank m n R
          (blockSum ((parabolicDiagonal hm hn R g).1, (parabolicDiagonal hm hn R g).2)) *
        Shahidi.swapRank m n R (Shahidi.upper n m R (parabolicShift hm hn R g x)) := by
    rw [← map_mul, ← map_mul, upper_mul_parabolic]
  rw [← Shahidi.blockWeyl_conjugate_blockSum m n R (parabolicDiagonal hm hn R g).1
    (parabolicDiagonal hm hn R g).2]
  simp only [Shahidi.intertwiningUnipotent]
  rw [mul_assoc, h1]
  group

/-- The block sum `diag(h, g)` lies in the standard parabolic of shape `(m, n)`. -/
theorem blockSum_mem_twoBlocks_parabolic (h : Langlands.GeneralLinear m R)
    (g : Langlands.GeneralLinear n R) :
    blockSum (h, g) ∈ (Shahidi.twoBlocks m n hm hn).parabolic R :=
  (Shahidi.twoBlocks_mem_parabolic_iff hm hn R _).mpr fun i j =>
    blockSum_apply_right_left h g i j

/-- Read through the rank exchange, an upper unipotent matrix lies in the standard
parabolic of the exchanged shape `(n, m)`. -/
theorem swapRank_symm_mem_parabolic (u : upperUnipotent (m + n) R) :
    (Shahidi.swapRank m n R).symm u.val ∈ (Shahidi.twoBlocks n m hn hm).parabolic R := by
  rw [Shahidi.twoBlocks_mem_parabolic_iff]
  intro i j
  have hlt : Fin.cast (Nat.add_comm n m) (j.castAdd m) <
      Fin.cast (Nat.add_comm n m) (i.natAdd n) := by
    rw [Fin.lt_def]
    simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    have := j.isLt
    omega
  exact UpperUnipotent.entry_eq_zero u hlt

/-- The affine map `x ↦ α⁻¹ (β + x δ)` as a homeomorphism of rectangular matrices. -/
def affineHomeomorph [TopologicalSpace R] [IsTopologicalRing R]
    (α : Langlands.GeneralLinear n R) (β : Matrix (Fin n) (Fin m) R)
    (δ : Langlands.GeneralLinear m R) :
    Matrix (Fin n) (Fin m) R ≃ₜ Matrix (Fin n) (Fin m) R where
  toFun x := (↑α⁻¹ : Matrix (Fin n) (Fin n) R) * (β + x * (↑δ : Matrix (Fin m) (Fin m) R))
  invFun z := ((↑α : Matrix (Fin n) (Fin n) R) * z - β) * (↑δ⁻¹ : Matrix (Fin m) (Fin m) R)
  left_inv x := by
    simp only
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, add_sub_cancel_left,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv z := by
    simp only
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, add_sub_cancel,
      ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun :=
    continuous_const.matrix_mul (continuous_const.add (continuous_id.matrix_mul continuous_const))
  continuous_invFun :=
    ((continuous_const.matrix_mul continuous_id).sub continuous_const).matrix_mul continuous_const

theorem affineHomeomorph_apply [TopologicalSpace R] [IsTopologicalRing R]
    (α : Langlands.GeneralLinear n R) (β : Matrix (Fin n) (Fin m) R)
    (δ : Langlands.GeneralLinear m R) (x : Matrix (Fin n) (Fin m) R) :
    affineHomeomorph R α β δ x =
      (↑α⁻¹ : Matrix (Fin n) (Fin n) R) * (β + x * (↑δ : Matrix (Fin m) (Fin m) R)) :=
  rfl

end Matrix

section Cell

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (a b : ℕ)

/-- The element `u` read in the parabolic of the exchanged shape `(B, A)`. -/
def exchangedParabolic (u : upperUnipotent (a + 1 + (b + 1)) F.Carrier) :
    (Shahidi.twoBlocks (b + 1) (a + 1) (Nat.succ_pos b) (Nat.succ_pos a)).parabolic F.Carrier :=
  ⟨(Shahidi.swapRank (a + 1) (b + 1) F.Carrier).symm u.val,
    swapRank_symm_mem_parabolic (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier u⟩

theorem swapRank_exchangedParabolic (u : upperUnipotent (a + 1 + (b + 1)) F.Carrier) :
    Shahidi.swapRank (a + 1) (b + 1) F.Carrier (exchangedParabolic F a b u).val = u.val :=
  (Shahidi.swapRank (a + 1) (b + 1) F.Carrier).apply_symm_apply u.val

/-- The Levi element `diag(δ, α)` of `P` attached to `u`. -/
def unipotentLeviFactor (u : upperUnipotent (a + 1 + (b + 1)) F.Carrier) :
    twoBlockParabolic F a b :=
  ⟨blockSum ((parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier
      (exchangedParabolic F a b u)).2,
    (parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier
      (exchangedParabolic F a b u)).1),
    blockSum_mem_twoBlocks_parabolic (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier _ _⟩

/-- The coordinate change `x ↦ α⁻¹ (β + x δ)` attached to `u`. -/
def unipotentShift (u : upperUnipotent (a + 1 + (b + 1)) F.Carrier)
    (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier :=
  parabolicShift (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier (exchangedParabolic F a b u) x

/-- `w n(x) u = diag(δ, α) w n(y)`, with `y` the shifted coordinate. -/
theorem twoBlockCellPoint_mul_upperUnipotent (u : upperUnipotent (a + 1 + (b + 1)) F.Carrier)
    (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    twoBlockCellPoint F a b x * u.val =
      (unipotentLeviFactor F a b u : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) *
        twoBlockCellPoint F a b (unipotentShift F a b u x) := by
  rw [twoBlockCellPoint, twoBlockCellPoint, ← swapRank_exchangedParabolic F a b u]
  exact blockWeyl_mul_intertwiningUnipotent_mul_swapRank (Nat.succ_pos a) (Nat.succ_pos b)
    F.Carrier x (exchangedParabolic F a b u)

/-- Right translation by an upper unipotent matrix preserves the cell. -/
theorem mul_upperUnipotent_mem_twoBlockCell
    {g : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier} (hg : g ∈ twoBlockCell F a b)
    (u : upperUnipotent (a + 1 + (b + 1)) F.Carrier) :
    g * u.val ∈ twoBlockCell F a b := by
  obtain ⟨q, x, rfl⟩ := hg
  refine ⟨q * unipotentLeviFactor F a b u, unipotentShift F a b u x, ?_⟩
  have h := twoBlockCellPoint_mul_upperUnipotent F a b u x
  rw [twoBlockCellPoint, twoBlockCellPoint] at h
  simp only [Subgroup.coe_mul, mul_assoc] at h ⊢
  rw [h]

end Cell

/-- JPSS (9.1), upper unipotent stability: right translation by every upper
unipotent matrix maps the cell submodule `D` into itself. -/
theorem twoBlockCellUnipotentStability : TwoBlockCellUnipotentStabilityStatement.{uF, uV} := by
  intro p _ F a b V₁ V₂ _ _ _ _ π₁ π₂ u f hf
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨hsupp, hcpt⟩ := hf
  refine ⟨fun g hg => ?_, ?_⟩
  · have h1 : g * u.val ∈ twoBlockCell F a b := hsupp hg
    have h2 := mul_upperUnipotent_mem_twoBlockCell F a b h1 u⁻¹
    rwa [Subgroup.coe_inv, mul_inv_cancel_right] at h2
  · let g' := exchangedParabolic F a b u
    let φ := affineHomeomorph F.Carrier
      (parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier g').1
      (parabolicCorner F.Carrier g'.val)
      (parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier g').2
    have hR : twoBlockRestriction F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ u.val f) =
        (twoBlockInducingRepresentation F a b π₁ π₂ (unipotentLeviFactor F a b u)) ∘
          (twoBlockRestriction F a b π₁ π₂ f) ∘ φ := by
      funext x
      change twoBlockEval F a b π₁ π₂ f (twoBlockCellPoint F a b x * u.val) =
        twoBlockInducingRepresentation F a b π₁ π₂ (unipotentLeviFactor F a b u)
          (twoBlockEval F a b π₁ π₂ f (twoBlockCellPoint F a b (unipotentShift F a b u x)))
      rw [twoBlockCellPoint_mul_upperUnipotent]
      exact f.1.2 (unipotentLeviFactor F a b u) _
    rw [hR]
    exact (hcpt.comp_homeomorph φ).comp_left (map_zero _)

end Langlands.Whittaker
