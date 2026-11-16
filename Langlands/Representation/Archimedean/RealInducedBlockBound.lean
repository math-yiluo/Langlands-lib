import Langlands.Representation.Archimedean.RealInducedBlockSlice
import Langlands.Representation.Archimedean.RealBlockJacquetFunctional
import Langlands.Representation.Archimedean.RealStandardModuleFourier

/-!
# Fourier coefficients along several disjoint induced blocks

Let `F` be a continuous right `O(N)`-finite function on `GL_N(ℝ)` and let `s₁, …, s_r` be
pairwise disjoint blocks of coordinates `p_i, p_i + 1`. Suppose that at every block `s_i`, `F` is
block covariant with exponents `α_i, α_i - (m_i + 1)`, that the Fourier modes `j` of `F` along the
rotations of `s_i` vanish unless `|j| ≥ m_i + 1` and `j ≡ m_i + 1 (mod 2)`, and that on `O(N)`
they vanish for `|j| > D`. Then for `k ∈ O(N)` the iterated Fourier coefficient
`Φ^{p_1}_{j_1} ⋯ Φ^{p_r}_{j_r} F` at `b_1(x_1, y_1, w_1) ⋯ b_r(x_r, y_r, w_r) k` is bounded by
`C · sup_{O(N)} |F| · ∏_i e^{(Re α_i - m_i/2)(x_i + y_i)} / |u_i|`,
`u_i = ((e^{x_i} + e^{y_i}) - i w_i)/2`, with a constant `C` depending only on the modes `j_i`,
the number of blocks and the degree bound `D` (`norm_coeffs_point_mul_le`).

The proof is by induction on the list of blocks, applying the one-block bound
`RealInducedBlockSlice.norm_blockFourierCoefficient_blockB_le` to the first block, with the
Fourier coefficients of `F` along the first block as the new functions for the remaining blocks.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

namespace RealInducedBlockBound

open RealBlockRotation RealBlockFourierFinite RealInducedBlockSlice RealBlockJacquet

variable {N : ℕ}

/-! ## Disjoint blocks commute -/

/-- The matrix which is `[[a, b], [c, d]]` on the block `p, p + 1` and `0` elsewhere. -/
def blockDelta {p : ℕ} (h : p + 1 < N) (a b c d : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if i = ia h then (if j = ia h then a else if j = ib h then b else 0)
    else if i = ib h then (if j = ia h then c else if j = ib h then d else 0)
    else 0

theorem blockMat_eq_one_add {p : ℕ} (h : p + 1 < N) (a b c d : ℝ) :
    blockMat h a b c d = 1 + blockDelta h (a - 1) b c (d - 1) := by
  ext i j
  simp only [blockMat, blockDelta, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, ia, ib,
    Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring1

theorem blockDelta_mul_blockDelta {p p' : ℕ} (h : p + 1 < N) (h' : p' + 1 < N)
    (hd : p + 1 < p' ∨ p' + 1 < p) (a b c d a' b' c' d' : ℝ) :
    blockDelta h a b c d * blockDelta h' a' b' c' d' = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [blockDelta, Matrix.of_apply, ia, ib, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring1

theorem blockMat_commute {p p' : ℕ} (h : p + 1 < N) (h' : p' + 1 < N)
    (hd : p + 1 < p' ∨ p' + 1 < p) (a b c d a' b' c' d' : ℝ) :
    blockMat h a b c d * blockMat h' a' b' c' d' =
      blockMat h' a' b' c' d' * blockMat h a b c d := by
  rw [blockMat_eq_one_add h, blockMat_eq_one_add h']
  simp only [add_mul, mul_add, one_mul, mul_one, blockDelta_mul_blockDelta h h' hd,
    blockDelta_mul_blockDelta h' h hd.symm, add_zero]
  abel

/-- A rotation in one block commutes with the upper triangular matrices of a disjoint block. -/
theorem blockRotation_mul_blockB_comm {p p' : ℕ} (h : p + 1 < N) (h' : p' + 1 < N)
    (hd : p + 1 < p' ∨ p' + 1 < p) (θ x y w : ℝ) :
    blockRotation N p θ * blockB h' x y w = blockB h' x y w * blockRotation N p θ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockRotation_eq_blockMat h, blockB_eq_blockMat h',
    blockMat_commute h h' hd]

/-! ## Fourier coefficients: elementary facts -/

/-- The right `O(N)`-finite functions. -/
def IsKFin (F : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
    (unitaryCompact ℝ N)

theorem blockFourierCoefficient_eq_zero_of {p : ℕ} (j : ℤ) {f : Langlands.GeneralLinear N ℝ → ℂ}
    {g : Langlands.GeneralLinear N ℝ} (h0 : ∀ θ : ℝ, f (blockRotation N p θ * g) = 0) :
    blockFourierCoefficient N p j f g = 0 := by
  unfold blockFourierCoefficient
  simp [h0]

theorem norm_blockFourierCoefficient_le {p : ℕ} (j : ℤ) {f : Langlands.GeneralLinear N ℝ → ℂ}
    {g : Langlands.GeneralLinear N ℝ} {B : ℝ}
    (hB : ∀ θ : ℝ, ‖f (blockRotation N p θ * g)‖ ≤ B) :
    ‖blockFourierCoefficient N p j f g‖ ≤ 2 * Real.pi * B := by
  unfold blockFourierCoefficient
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (C := B) (f := fun θ : ℝ =>
      f (blockRotation N p θ * g) * Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)))
    (fun θ _ => by
      have hn : ‖Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [norm_mul, hn, mul_one]
      exact hB θ)
  rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
  linarith

/-- Block Fourier coefficients of a continuous `O(N)`-finite function are `O(N)`-finite. -/
theorem isKFin_blockFourierCoefficient {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    (hK : IsKFin F) (p : ℕ) (j : ℤ) : IsKFin (blockFourierCoefficient N p j F) := by
  set ρ := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
  set V := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ N => ρ (k : _) F)
  have : FiniteDimensional ℂ V := hK
  have hcont : ∀ v ∈ V, Continuous v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hF.comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul a x _ hx => exact hx.const_smul a
  let L : V →ₗ[ℂ] (Langlands.GeneralLinear N ℝ → ℂ) :=
    { toFun := fun v => blockFourierCoefficient N p j v.1
      map_add' := fun v w => by
        funext g
        exact blockFourierCoefficient_add p j (hcont _ v.2) (hcont _ w.2) g
      map_smul' := fun a v => by
        funext g
        exact blockFourierCoefficient_smul p j a v.1 g }
  rw [IsKFin, mem_kFiniteVectors_iff]
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨⟨ρ (k : _) F, Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
  funext g
  exact blockFourierCoefficient_rightTranslation N p j F k g

/-- Left translates of `O(N)`-finite functions are `O(N)`-finite. -/
theorem isKFin_leftTranslate {F : Langlands.GeneralLinear N ℝ → ℂ} (hK : IsKFin F)
    (Y : Langlands.GeneralLinear N ℝ) : IsKFin fun y => F (Y * y) := by
  set ρ := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
  set V := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ N => ρ (k : _) F)
  have : FiniteDimensional ℂ V := hK
  let lY : (Langlands.GeneralLinear N ℝ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear N ℝ → ℂ) :=
    { toFun := fun f y => f (Y * y)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [IsKFin, mem_kFiniteVectors_iff]
  refine Submodule.finiteDimensional_of_le (S₂ := V.map lY) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine Submodule.mem_map.mpr ⟨ρ (k : _) F, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  funext y
  show F (Y * y * k) = F (Y * (y * k))
  rw [mul_assoc]

/-- Block covariance is preserved by Fourier coefficients along a disjoint block. -/
theorem isBlockCovariant_blockFourierCoefficient {p p' : ℕ} (h : p + 1 < N) (h' : p' + 1 < N)
    (hd : p + 1 < p' ∨ p' + 1 < p) {α β : ℂ} {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : IsBlockCovariant h α β F) (j : ℤ) :
    IsBlockCovariant h α β (blockFourierCoefficient N p' j F) := by
  intro x y w g
  unfold blockFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  show F (blockRotation N p' θ * (blockB h x y w * g)) * _ = _ * (F (blockRotation N p' θ * g) * _)
  rw [← mul_assoc, blockRotation_mul_blockB_comm h' h hd.symm θ x y w, mul_assoc, hF, mul_assoc]

/-! ## Lists of blocks -/

/-- A block `p, p + 1` with covariance exponent `α` and weight `m`, together with a Fourier mode
`j` and the coordinates `x, y, w` of an upper triangular matrix `b(x, y, w)` on the block. -/
structure Slot (N : ℕ) where
  /-- The first coordinate of the block. -/
  p : ℕ
  hp : p + 1 < N
  /-- The covariance exponent at the coordinate `p`. -/
  α : ℂ
  /-- The weight of the block. -/
  M : ℕ
  /-- The Fourier mode. -/
  j : ℤ
  /-- The logarithm of the first diagonal entry of `b`. -/
  x : ℝ
  /-- The logarithm of the second diagonal entry of `b`. -/
  y : ℝ
  /-- The upper right entry of `b`. -/
  w : ℝ

/-- Two slots occupy disjoint blocks. -/
def Slot.Disjoint (s t : Slot N) : Prop :=
  s.p + 1 < t.p ∨ t.p + 1 < s.p

/-- The iterated Fourier coefficient `Φ^{p_1}_{j_1} ⋯ Φ^{p_r}_{j_r} F`. -/
def coeffs : List (Slot N) → (Langlands.GeneralLinear N ℝ → ℂ) → Langlands.GeneralLinear N ℝ → ℂ
  | [], F => F
  | s :: rest, F => blockFourierCoefficient N s.p s.j (coeffs rest F)

/-- The product `b_1(x_1, y_1, w_1) ⋯ b_r(x_r, y_r, w_r)`. -/
def point : List (Slot N) → Langlands.GeneralLinear N ℝ
  | [] => 1
  | s :: rest => blockB s.hp s.x s.y s.w * point rest

/-- The bound `∏_i e^{(Re α_i - m_i/2)(x_i + y_i)} / |u_i|`,
`u_i = ((e^{x_i} + e^{y_i}) - i w_i)/2`. -/
def expBound (slots : List (Slot N)) : ℝ :=
  (slots.map fun s =>
    Real.exp ((s.α.re - s.M / 2) * (s.x + s.y)) / ‖waveU s.x s.y s.w‖).prod

/-- The constant `∏_i 2^{|j_i| + 2D} (2D + 1) 2π`. -/
def const (slots : List (Slot N)) (D : ℕ) : ℝ :=
  (slots.map fun s =>
    (2 : ℝ) ^ (s.j.natAbs + 2 * D) * (2 * (D : ℝ) + 1) * (2 * Real.pi)).prod

/-- The admissible Fourier modes `±(m + 1 + 2l)` of a block of weight `m`. -/
def IsMode (M : ℕ) (j : ℤ) : Prop :=
  ∃ l : ℕ, j = ((M + 1 + 2 * l : ℕ) : ℤ) ∨ j = -((M + 1 + 2 * l : ℕ) : ℤ)

/-- The conditions at one block: covariance, admissible modes, and the degree bound `D` on
`O(N)`. -/
def SlotCond (s : Slot N) (D : ℕ) (F : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  IsBlockCovariant s.hp s.α (s.α - (s.M + 1)) F ∧
    (∀ j : ℤ, ¬ IsMode s.M j → ∀ g, blockFourierCoefficient N s.p j F g = 0) ∧
    ∀ j : ℤ, (D : ℤ) < |j| → ∀ k ∈ unitaryCompact ℝ N, blockFourierCoefficient N s.p j F k = 0

/-- The class of functions of the bound: continuous, `O(N)`-finite, and satisfying the
conditions at every block of the list. -/
def InClass (slots : List (Slot N)) (D : ℕ) (F : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  Continuous F ∧ IsKFin F ∧ ∀ s ∈ slots, SlotCond s D F

theorem continuous_coeffs {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) :
    ∀ slots : List (Slot N), Continuous (coeffs slots F)
  | [] => hF
  | s :: rest => continuous_blockFourierCoefficient s.p s.j (continuous_coeffs hF rest)

theorem isKFin_coeffs {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) (hK : IsKFin F) :
    ∀ slots : List (Slot N), IsKFin (coeffs slots F)
  | [] => hK
  | s :: rest =>
    isKFin_blockFourierCoefficient (continuous_coeffs hF rest) (isKFin_coeffs hF hK rest) s.p s.j

theorem blockRotation_mul_point {p : ℕ} (h : p + 1 < N) (θ : ℝ) :
    ∀ rest : List (Slot N), (∀ t ∈ rest, p + 1 < t.p ∨ t.p + 1 < p) →
      blockRotation N p θ * point rest = point rest * blockRotation N p θ
  | [], _ => by simp [point]
  | t :: rest, hd => by
    rw [point, ← mul_assoc, blockRotation_mul_blockB_comm h t.hp (hd t List.mem_cons_self),
      mul_assoc, blockRotation_mul_point h θ rest fun t' ht' => hd t' (List.mem_cons_of_mem _ ht'),
      mul_assoc]

theorem blockFourierCoefficient_coeffs {p : ℕ} (j : ℤ) {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F) :
    ∀ rest : List (Slot N), (∀ t ∈ rest, p + 1 < t.p ∨ t.p + 1 < p) →
      blockFourierCoefficient N p j (coeffs rest F) = coeffs rest (blockFourierCoefficient N p j F)
  | [], _ => rfl
  | t :: rest, hd => by
    funext g
    simp only [coeffs]
    rw [blockFourierCoefficient_comm (hd t List.mem_cons_self) (continuous_coeffs hF rest),
      blockFourierCoefficient_coeffs j hF rest fun t' ht' => hd t' (List.mem_cons_of_mem _ ht')]

theorem isBlockCovariant_coeffs {p : ℕ} (h : p + 1 < N) {α β : ℂ}
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : IsBlockCovariant h α β F) :
    ∀ rest : List (Slot N), (∀ t ∈ rest, p + 1 < t.p ∨ t.p + 1 < p) →
      IsBlockCovariant h α β (coeffs rest F)
  | [], _ => hF
  | t :: rest, hd =>
    isBlockCovariant_blockFourierCoefficient h t.hp (hd t List.mem_cons_self)
      (isBlockCovariant_coeffs h hF rest fun t' ht' => hd t' (List.mem_cons_of_mem _ ht')) t.j

/-- The conditions at a block `t` are preserved by Fourier coefficients along a disjoint block. -/
theorem slotCond_blockFourierCoefficient {s t : Slot N} (hd : s.p + 1 < t.p ∨ t.p + 1 < s.p)
    {D : ℕ} {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F) (ht : SlotCond t D F)
    (j : ℤ) : SlotCond t D (blockFourierCoefficient N s.p j F) := by
  refine ⟨isBlockCovariant_blockFourierCoefficient t.hp s.hp hd.symm ht.1 j, ?_, ?_⟩
  · intro j' hj' g
    rw [← blockFourierCoefficient_comm hd hF j j' g]
    have h0 : blockFourierCoefficient N t.p j' F = 0 := funext (ht.2.1 j' hj')
    rw [h0, blockFourierCoefficient_zero_fun]
  · intro j' hj' k hk
    rw [← blockFourierCoefficient_comm hd hF j j' k]
    exact blockFourierCoefficient_eq_zero_of j fun θ =>
      ht.2.2 j' hj' _ (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk)

/-! ## The bound -/

theorem card_filter_abs_le (D D' : ℕ) :
    ((Finset.Icc (-(D' : ℤ)) D').filter fun j => |j| ≤ (D : ℤ)).card ≤ 2 * D + 1 := by
  calc ((Finset.Icc (-(D' : ℤ)) D').filter fun j => |j| ≤ (D : ℤ)).card ≤
        (Finset.Icc (-(D : ℤ)) D).card := by
        refine Finset.card_le_card fun j hj => ?_
        rw [Finset.mem_Icc, ← abs_le]
        exact (Finset.mem_filter.mp hj).2
    _ = 2 * D + 1 := by
        rw [Int.card_Icc]
        omega

/-- **The multi-block bound.** For pairwise disjoint blocks and a function `F` of the class
`InClass slots D` bounded by `B` on `O(N)`, the iterated Fourier coefficient at
`b_1 ⋯ b_r k`, `k ∈ O(N)`, is bounded by `const slots D * B * expBound slots`. -/
theorem norm_coeffs_point_mul_le (D : ℕ) :
    ∀ (slots : List (Slot N)), slots.Pairwise Slot.Disjoint →
      ∀ (F : Langlands.GeneralLinear N ℝ → ℂ) (B : ℝ), InClass slots D F →
        (∀ k ∈ unitaryCompact ℝ N, ‖F k‖ ≤ B) →
        ∀ k ∈ unitaryCompact ℝ N,
          ‖coeffs slots F (point slots * k)‖ ≤ const slots D * B * expBound slots
  | [], _, F, B, _, hB, k, hk => by
    simp only [coeffs, point, const, expBound, List.map_nil, List.prod_nil, one_mul, mul_one]
    exact hB k hk
  | s :: rest, hpw, F, B, hF, hB, k, hk => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hsd' : ∀ t ∈ rest, s.p + 1 < t.p ∨ t.p + 1 < s.p := hsd
    obtain ⟨hF0, hFK, hFs⟩ := hF
    have hs := hFs s List.mem_cons_self
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 (one_mem _))
    have hcls : ∀ j, InClass rest D (blockFourierCoefficient N s.p j F) := fun j =>
      ⟨continuous_blockFourierCoefficient _ _ hF0, isKFin_blockFourierCoefficient hF0 hFK _ _,
        fun t ht => slotCond_blockFourierCoefficient (hsd' t ht) hF0
          (hFs t (List.mem_cons_of_mem _ ht)) j⟩
    have hGc : Continuous (coeffs rest F) := continuous_coeffs hF0 rest
    have hGK : IsKFin (coeffs rest F) := isKFin_coeffs hF0 hFK rest
    obtain ⟨D', -, hsum⟩ := exists_eq_sum_blockFourierCoefficient s.hp
      (f := fun y => coeffs rest F (point rest * y))
      (hGc.comp (continuous_const.mul continuous_id)) (isKFin_leftTranslate hGK (point rest))
    have hc : ∀ j, blockFourierCoefficient N s.p j (fun y => coeffs rest F (point rest * y)) k =
        coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k) := by
      intro j
      have e : blockFourierCoefficient N s.p j (fun y => coeffs rest F (point rest * y)) k =
          blockFourierCoefficient N s.p j (coeffs rest F) (point rest * k) := by
        unfold blockFourierCoefficient
        refine intervalIntegral.integral_congr fun θ _ => ?_
        simp only
        rw [← mul_assoc, ← mul_assoc, blockRotation_mul_point s.hp θ rest hsd']
      rw [e, blockFourierCoefficient_coeffs j hF0 rest hsd']
    have hzero : ∀ j, (¬ IsMode s.M j ∨ (D : ℤ) < |j|) →
        coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k) = 0 := by
      intro j hj
      have := norm_coeffs_point_mul_le D rest hrest (blockFourierCoefficient N s.p j F) 0 (hcls j)
        (fun k' hk' => by
          rcases hj with hj | hj
          · rw [hs.2.1 j hj k', norm_zero]
          · rw [hs.2.2 j hj k' hk', norm_zero]) k hk
      rw [mul_zero, zero_mul] at this
      exact norm_le_zero_iff.mp this
    have hbound : ∀ j, ‖coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k)‖ ≤
        const rest D * (2 * Real.pi * B) * expBound rest := fun j =>
      norm_coeffs_point_mul_le D rest hrest _ _ (hcls j)
        (fun k' hk' => norm_blockFourierCoefficient_le j fun θ =>
          hB _ (mul_mem (blockRotation_mem_unitaryCompact N s.p θ) hk')) k hk
    set S := (Finset.Icc (-(D' : ℤ)) D').filter fun j => |j| ≤ (D : ℤ) with hS
    have hexp : ∀ φ : ℝ, coeffs rest F (blockRotation N s.p φ * (point rest * k)) =
        (2 * (Real.pi : ℂ))⁻¹ * ∑ j ∈ S,
          coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k) * expMode j φ := by
      intro φ
      rw [← mul_assoc, blockRotation_mul_point s.hp φ rest hsd', mul_assoc]
      refine (hsum k hk φ).trans ?_
      congr 1
      simp_rw [hc]
      refine (Finset.sum_filter_of_ne fun j _ hne => ?_).symm
      by_contra hj
      exact hne (by rw [hzero j (Or.inr (not_le.mp hj)), zero_mul])
    have hD : ∀ j ∈ S, |j| ≤ (D : ℤ) := fun j hj => (Finset.mem_filter.mp hj).2
    have hmode : ∀ j ∈ S, coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k) ≠ 0 →
        IsMode s.M j := fun j _ hne => by
      by_contra hj
      exact hne (hzero j (Or.inl hj))
    have hcov : IsBlockCovariant s.hp s.α (s.α - (s.M + 1)) (coeffs rest F) :=
      isBlockCovariant_coeffs s.hp hs.1 rest hsd'
    have key := norm_blockFourierCoefficient_blockB_le s.hp (by ring) hcov (point rest * k) S
      (fun j => coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k)) hexp hD hmode
      s.j s.x s.y s.w
    set X := const rest D * (2 * Real.pi * B) * expBound rest with hX
    have hX0 : 0 ≤ X := (norm_nonneg _).trans (hbound 0)
    have hsumc : ∑ j ∈ S, ‖coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k)‖ ≤
        (2 * (D : ℝ) + 1) * X := by
      calc ∑ j ∈ S, ‖coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k)‖ ≤
            S.card • X := Finset.sum_le_card_nsmul _ _ _ fun j _ => hbound j
        _ = (S.card : ℝ) * X := nsmul_eq_mul _ _
        _ ≤ (2 * (D : ℝ) + 1) * X := by
            gcongr
            exact_mod_cast card_filter_abs_le D D'
    show ‖blockFourierCoefficient N s.p s.j (coeffs rest F)
      (blockB s.hp s.x s.y s.w * point rest * k)‖ ≤ _
    rw [mul_assoc]
    calc _ ≤ 2 ^ (s.j.natAbs + 2 * D) *
          (∑ j ∈ S, ‖coeffs rest (blockFourierCoefficient N s.p j F) (point rest * k)‖) *
          (Real.exp ((s.α.re - s.M / 2) * (s.x + s.y)) / ‖waveU s.x s.y s.w‖) := key
      _ ≤ 2 ^ (s.j.natAbs + 2 * D) * ((2 * (D : ℝ) + 1) * X) *
          (Real.exp ((s.α.re - s.M / 2) * (s.x + s.y)) / ‖waveU s.x s.y s.w‖) := by
          have := norm_waveU_pos s.x s.y s.w
          gcongr
      _ = const (s :: rest) D * B * expBound (s :: rest) := by
          simp only [hX, const, expBound, List.map_cons, List.prod_cons]
          ring

end RealInducedBlockBound

open RealInducedBlockBound in
/-- **Multi-block bound for induced blocks.** For pairwise disjoint slots and a function `F` in
`InClass slots D` with `|F| ≤ B` on `O(N)`, the iterated Fourier coefficient
`coeffs slots F` at `point slots * k`, `k ∈ O(N)`, is at most
`const slots D * B * expBound slots`. -/
def RealInducedBlockBoundStatement : Prop :=
  ∀ (N D : ℕ) (slots : List (Slot N)), slots.Pairwise Slot.Disjoint →
    ∀ (F : Langlands.GeneralLinear N ℝ → ℂ) (B : ℝ), InClass slots D F →
      (∀ k ∈ unitaryCompact ℝ N, ‖F k‖ ≤ B) →
      ∀ k ∈ unitaryCompact ℝ N,
        ‖coeffs slots F (point slots * k)‖ ≤ const slots D * B * expBound slots

theorem realInducedBlockBound : RealInducedBlockBoundStatement :=
  fun _ D slots hpw F B hF hB k hk =>
    RealInducedBlockBound.norm_coeffs_point_mul_le D slots hpw F B hF hB k hk

end Langlands.Archimedean
