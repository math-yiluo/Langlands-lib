import Langlands.Representation.Archimedean.RealOrthogonalUncertainty

/-!
# Adjacent-rotation uncertainty in arbitrary ambient rank

A three-coordinate block embedding transfers the published rank-three orthogonal uncertainty
principle to adjacent coordinate rotations in any ambient rank. Restriction at a compact right
coset preserves right compact finiteness.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealOrthogonalBlock

open Langlands.GeneralLinear RealBlockRotation

variable {n : ℕ} (p : ℕ) (hp : p + 3 ≤ n)

/-! ## The block embedding on matrices -/

/-- The three consecutive positions starting at `p`. -/
def pos (k : Fin 3) : Fin n := ⟨p + k, by omega⟩

theorem pos_val (k : Fin 3) : ((pos p hp k : Fin n) : ℕ) = p + k := rfl

theorem pos_injective : Function.Injective (pos p hp) := by
  intro k l h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simp only [pos_val] at h'
  omega

theorem pos_lt_pos_iff (k l : Fin 3) : pos p hp k < pos p hp l ↔ k < l := by
  rw [Fin.lt_def, Fin.lt_def, pos_val, pos_val]
  omega

theorem pos_eq_pos_iff (k l : Fin 3) : pos p hp k = pos p hp l ↔ k = l :=
  (pos_injective p hp).eq_iff

/-- Every position is in the block or not. -/
theorem mem_range_or (a : Fin n) : (∃ k, a = pos p hp k) ∨ ∀ k, a ≠ pos p hp k := by
  by_cases h : ∃ k, a = pos p hp k
  · exact Or.inl h
  · push Not at h
    exact Or.inr h

/-- The `n × 3` matrix of the inclusion of the coordinates `p`, `p + 1`, `p + 2`. -/
def incl : Matrix (Fin n) (Fin 3) ℝ := Matrix.of fun a k => if a = pos p hp k then 1 else 0

/-- `X ↦ P X Pᵀ`: the `3 × 3` matrix `X` in rows and columns `p`, `p + 1`, `p + 2`, zero elsewhere. -/
def lin (X : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  incl p hp * X * (incl p hp)ᵀ

theorem lin_apply (X : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin n) :
    lin p hp X a b = ∑ l, (∑ k, (if a = pos p hp k then 1 else 0) * X k l) *
      (if b = pos p hp l then 1 else 0) := by
  simp only [lin, Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply]

theorem lin_apply_pos (X : Matrix (Fin 3) (Fin 3) ℝ) (k l : Fin 3) :
    lin p hp X (pos p hp k) (pos p hp l) = X k l := by
  rw [lin_apply]
  simp [pos_eq_pos_iff]

theorem lin_apply_left (X : Matrix (Fin 3) (Fin 3) ℝ) {a : Fin n} (ha : ∀ k, a ≠ pos p hp k)
    (b : Fin n) : lin p hp X a b = 0 := by
  rw [lin_apply]
  simp [ha]

theorem lin_apply_right (X : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin n) {b : Fin n}
    (hb : ∀ k, b ≠ pos p hp k) : lin p hp X a b = 0 := by
  rw [lin_apply]
  simp [hb]

theorem inclT_mul_incl : (incl p hp)ᵀ * incl p hp = 1 := by
  ext k l
  simp only [Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply]
  simp [pos_eq_pos_iff, eq_comm]

theorem lin_mul (X Y : Matrix (Fin 3) (Fin 3) ℝ) : lin p hp X * lin p hp Y = lin p hp (X * Y) := by
  simp only [lin]
  calc incl p hp * X * (incl p hp)ᵀ * (incl p hp * Y * (incl p hp)ᵀ)
      = incl p hp * X * ((incl p hp)ᵀ * incl p hp) * Y * (incl p hp)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = incl p hp * (X * Y) * (incl p hp)ᵀ := by
        rw [inclT_mul_incl, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem lin_add (X Y : Matrix (Fin 3) (Fin 3) ℝ) : lin p hp (X + Y) = lin p hp X + lin p hp Y := by
  simp only [lin, Matrix.mul_add, Matrix.add_mul]

theorem lin_sub (X Y : Matrix (Fin 3) (Fin 3) ℝ) : lin p hp (X - Y) = lin p hp X - lin p hp Y := by
  simp only [lin, Matrix.mul_sub, Matrix.sub_mul]

theorem lin_zero : lin p hp (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  simp [lin]

theorem lin_smul (c : ℝ) (X : Matrix (Fin 3) (Fin 3) ℝ) : lin p hp (c • X) = c • lin p hp X := by
  simp only [lin, Matrix.mul_smul, Matrix.smul_mul]

theorem lin_single (k l : Fin 3) (c : ℝ) :
    lin p hp (Matrix.single k l c) = Matrix.single (pos p hp k) (pos p hp l) c := by
  ext a b
  rcases mem_range_or p hp a with ⟨k', rfl⟩ | ha
  · rcases mem_range_or p hp b with ⟨l', rfl⟩ | hb
    · rw [lin_apply_pos]
      simp [Matrix.single_apply, pos_eq_pos_iff]
    · rw [lin_apply_right p hp _ _ hb]
      simp [(hb l).symm]
  · rw [lin_apply_left p hp _ ha]
    simp [(ha k).symm]

theorem incl_conjTranspose : (incl p hp)ᴴ = (incl p hp)ᵀ := by
  ext k a
  simp [incl, Matrix.conjTranspose_apply]

theorem star_lin (X : Matrix (Fin 3) (Fin 3) ℝ) : star (lin p hp X) = lin p hp (star X) := by
  ext a b
  rw [Matrix.star_apply]
  rcases mem_range_or p hp a with ⟨k, rfl⟩ | ha
  · rcases mem_range_or p hp b with ⟨l, rfl⟩ | hb
    · rw [lin_apply_pos, lin_apply_pos, Matrix.star_apply]
    · rw [lin_apply_left p hp _ hb, lin_apply_right p hp _ _ hb, star_zero]
  · rw [lin_apply_right p hp _ _ ha, lin_apply_left p hp _ ha, star_zero]

/-! ## The block embedding `GL_3(ℝ) → GL_n(ℝ)` -/

/-- `M ↦ P M Pᵀ + (1 - P Pᵀ)`: the identity matrix with the block `M` in rows and columns
`p`, `p + 1`, `p + 2`. -/
def blockMat (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lin p hp M + (1 - lin p hp 1)

theorem lin_mul_compl (M : Matrix (Fin 3) (Fin 3) ℝ) :
    lin p hp M * (1 - lin p hp 1) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, lin_mul, Matrix.mul_one, sub_self]

theorem compl_mul_lin (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (1 - lin p hp 1) * lin p hp M = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, lin_mul, Matrix.one_mul, sub_self]

theorem compl_mul_compl : (1 - lin p hp 1) * (1 - lin p hp 1) = (1 - lin p hp 1 :
    Matrix (Fin n) (Fin n) ℝ) := by
  rw [Matrix.sub_mul, Matrix.one_mul, lin_mul_compl, sub_zero]

theorem blockMat_mul (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    blockMat p hp M * blockMat p hp N = blockMat p hp (M * N) := by
  rw [blockMat, blockMat, blockMat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, lin_mul,
    lin_mul_compl, compl_mul_lin, compl_mul_compl, add_zero, zero_add]

theorem blockMat_one : blockMat p hp (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  rw [blockMat, add_sub_cancel]

theorem blockMat_mul_lin (M X : Matrix (Fin 3) (Fin 3) ℝ) :
    blockMat p hp M * lin p hp X = lin p hp (M * X) := by
  rw [blockMat, Matrix.add_mul, lin_mul, compl_mul_lin, add_zero]

theorem blockMat_add_lin (M X : Matrix (Fin 3) (Fin 3) ℝ) :
    blockMat p hp (M + X) = blockMat p hp M + lin p hp X := by
  rw [blockMat, blockMat, lin_add]
  abel

theorem star_blockMat (M : Matrix (Fin 3) (Fin 3) ℝ) :
    star (blockMat p hp M) = blockMat p hp (star M) := by
  rw [blockMat, blockMat, star_add, star_sub, star_one, star_lin, star_lin, star_one]

theorem blockMat_apply_pos (M : Matrix (Fin 3) (Fin 3) ℝ) (k l : Fin 3) :
    blockMat p hp M (pos p hp k) (pos p hp l) = M k l := by
  simp only [blockMat, Matrix.add_apply, Matrix.sub_apply, lin_apply_pos, Matrix.one_apply,
    pos_eq_pos_iff]
  ring

theorem blockMat_apply_left (M : Matrix (Fin 3) (Fin 3) ℝ) {a : Fin n}
    (ha : ∀ k, a ≠ pos p hp k) (b : Fin n) :
    blockMat p hp M a b = (1 : Matrix (Fin n) (Fin n) ℝ) a b := by
  simp only [blockMat, Matrix.add_apply, Matrix.sub_apply, lin_apply_left p hp _ ha]
  ring

theorem blockMat_apply_right (M : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin n) {b : Fin n}
    (hb : ∀ k, b ≠ pos p hp k) :
    blockMat p hp M a b = (1 : Matrix (Fin n) (Fin n) ℝ) a b := by
  simp only [blockMat, Matrix.add_apply, Matrix.sub_apply, lin_apply_right p hp _ _ hb]
  ring

/-- `blockMat` as a monoid homomorphism. -/
def blockHom : Matrix (Fin 3) (Fin 3) ℝ →* Matrix (Fin n) (Fin n) ℝ where
  toFun := blockMat p hp
  map_one' := blockMat_one p hp
  map_mul' M N := (blockMat_mul p hp M N).symm

/-- The block embedding `GL_3(ℝ) → GL_n(ℝ)` at the positions `p`, `p + 1`, `p + 2`. -/
def block : Langlands.GeneralLinear 3 ℝ →* Langlands.GeneralLinear n ℝ :=
  Units.map (blockHom p hp)

theorem block_val (g : Langlands.GeneralLinear 3 ℝ) :
    ((block p hp g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      blockMat p hp (g : Matrix (Fin 3) (Fin 3) ℝ) :=
  rfl

theorem block_injective : Function.Injective (block p hp) := by
  intro g h heq
  apply Units.ext
  ext i j
  have he := congrArg (fun u : Langlands.GeneralLinear n ℝ =>
    (u : Matrix (Fin n) (Fin n) ℝ) (pos p hp i) (pos p hp j)) heq
  simpa only [block_val, blockMat_apply_pos] using he

theorem block_mem_unitaryCompact {g : Langlands.GeneralLinear 3 ℝ}
    (hg : g ∈ unitaryCompact ℝ 3) : block p hp g ∈ unitaryCompact ℝ n := by
  rw [mem_unitaryCompact_iff] at hg ⊢
  rw [block_val, star_blockMat, blockMat_mul, hg, blockMat_one]


/-- Restriction to the embedded block at a fixed right coset. -/
def restrictCoset (k : Langlands.GeneralLinear n ℝ) :
    (Langlands.GeneralLinear n ℝ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear 3 ℝ → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun g => block p hp g * k)

theorem restrictCoset_apply (k : Langlands.GeneralLinear n ℝ)
    (f : Langlands.GeneralLinear n ℝ → ℂ) (g : Langlands.GeneralLinear 3 ℝ) :
    restrictCoset p hp k f g = f (block p hp g * k) := rfl

theorem continuous_blockMat : Continuous (blockMat p hp) := by
  unfold blockMat lin
  fun_prop

theorem continuous_block : Continuous (block p hp) := by
  apply Units.continuous_iff.mpr
  exact ⟨(continuous_blockMat p hp).comp Units.continuous_val,
    (continuous_blockMat p hp).comp Units.continuous_coe_inv⟩

theorem continuous_restrictCoset (k : Langlands.GeneralLinear n ℝ)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f) :
    Continuous (restrictCoset p hp k f) :=
  hf.comp ((continuous_block p hp).mul continuous_const)

theorem restrictCoset_mem_kFiniteVectors {k : Langlands.GeneralLinear n ℝ}
    (hk : k ∈ unitaryCompact ℝ n) {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n)) :
    restrictCoset p hp k f ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
        (unitaryCompact ℝ 3) := by
  rw [mem_kFiniteVectors_iff] at hf ⊢
  have hle : Submodule.span ℂ (Set.range fun u : unitaryCompact ℝ 3 =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ)
          (u : Langlands.GeneralLinear 3 ℝ) (restrictCoset p hp k f)) ≤
      (Submodule.span ℂ (Set.range fun u : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (u : Langlands.GeneralLinear n ℝ) f)).map (restrictCoset p hp k) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    have hku : k⁻¹ * block p hp u * k ∈ unitaryCompact ℝ n :=
      (unitaryCompact ℝ n).mul_mem
        ((unitaryCompact ℝ n).mul_mem ((unitaryCompact ℝ n).inv_mem hk)
          (block_mem_unitaryCompact p hp u.2)) hk
    refine ⟨_, Submodule.subset_span ⟨⟨_, hku⟩, rfl⟩, ?_⟩
    funext g
    change f ((block p hp g * k) * (k⁻¹ * block p hp u * k)) =
      f (block p hp (g * u) * k)
    rw [map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]
  exact Submodule.finiteDimensional_of_le hle


/-! ## Compatibility with the two coordinate rotations -/

theorem pos_ia {q : ℕ} (hq : q + 1 < 3) :
    pos p hp (ia hq) = ia (show p + q + 1 < n by omega) := by
  apply Fin.ext
  rfl

theorem pos_ib {q : ℕ} (hq : q + 1 < 3) :
    pos p hp (ib hq) = ib (show p + q + 1 < n by omega) := by
  apply Fin.ext
  dsimp [pos, ib]
  omega

theorem lin_blockProj {q : ℕ} (hq : q + 1 < 3) :
    lin p hp (blockProj hq) = blockProj (show p + q + 1 < n by omega) := by
  rw [blockProj, lin_add, lin_single, lin_single, pos_ia, pos_ib, blockProj]

theorem lin_rotationGenerator {q : ℕ} (hq : q + 1 < 3) :
    lin p hp (rotationGenerator 3 q) = rotationGenerator n (p + q) := by
  rw [rotationGenerator_eq hq, lin_sub, lin_single, lin_single, pos_ia, pos_ib,
    rotationGenerator_eq (show p + q + 1 < n by omega)]

theorem blockMat_blockRotation {q : ℕ} (hq : q + 1 < 3) (θ : ℝ) :
    blockMat p hp (blockRotation 3 q θ : Matrix (Fin 3) (Fin 3) ℝ) =
      (blockRotation n (p + q) θ : Matrix (Fin n) (Fin n) ℝ) := by
  rw [blockRotation_val_eq hq,
    blockRotation_val_eq (show p + q + 1 < n by omega), rotMatrix, rotMatrix,
    blockMat, lin_add, lin_add, lin_smul, lin_smul, lin_blockProj p hp hq, lin_rotationGenerator p hp hq]
  abel

theorem block_blockRotation {q : ℕ} (hq : q + 1 < 3) (θ : ℝ) :
    block p hp (blockRotation 3 q θ) = blockRotation n (p + q) θ := by
  apply Units.ext
  rw [block_val, blockMat_blockRotation p hp hq]

theorem blockFourierCoefficient_restrictCoset {q : ℕ} (hq : q + 1 < 3)
    (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ)
    (j : ℤ) (g : Langlands.GeneralLinear 3 ℝ) :
    blockFourierCoefficient 3 q j (restrictCoset p hp k f) g =
      blockFourierCoefficient n (p + q) j f (block p hp g * k) := by
  unfold blockFourierCoefficient
  congr 1
  funext θ
  rw [restrictCoset_apply, map_mul, block_blockRotation p hp hq, mul_assoc]

include hp in
/-- High modes for one rotation and strictly lower modes for its adjacent rotation force
vanishing on the ambient orthogonal group. -/
theorem adjacent_uncertainty {r s m m' : ℕ}
    (hrs : r = 0 ∧ s = 1 ∨ r = 1 ∧ s = 0) (hmm : m' < m)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (hhigh : ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, |j| < (m : ℤ) →
      blockFourierCoefficient n (p + r) j f g = 0)
    (hlow : ∀ g ∈ unitaryCompact ℝ n, ∀ j : ℤ, (m' : ℤ) ≤ |j| →
      blockFourierCoefficient n (p + s) j f g = 0) :
    ∀ k ∈ unitaryCompact ℝ n, f k = 0 := by
  intro k hk
  have hr : r + 1 < 3 := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hs : s + 1 < 3 := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hzero := RealOrthogonalUncertainty.realOrthogonalBlockUncertainty r s m m'
    (restrictCoset p hp k f) hrs hmm (continuous_restrictCoset p hp k hf)
      (restrictCoset_mem_kFiniteVectors p hp hk hK) ?_ ?_ 1 (one_mem _)
  · simpa [restrictCoset_apply] using hzero
  · intro g hg j hj
    rw [blockFourierCoefficient_restrictCoset p hp hr]
    exact hhigh _ ((unitaryCompact ℝ n).mul_mem (block_mem_unitaryCompact p hp hg) hk) j hj
  · intro g hg j hj
    rw [blockFourierCoefficient_restrictCoset p hp hs]
    exact hlow _ ((unitaryCompact ℝ n).mul_mem (block_mem_unitaryCompact p hp hg) hk) j hj

end Langlands.Archimedean.RealOrthogonalBlock
