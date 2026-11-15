import Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrdering

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

namespace RankOneBlock

/-! ## The block embedding at rows and columns `i, j` -/

section Block

variable {n : ℕ} (i j : Fin n)

/-- The `2 × n` matrix with `1` at `(0, i)` and `(1, j)`. -/
def proj : Matrix (Fin 2) (Fin n) ℂ :=
  Matrix.of fun p a => if a = ![i, j] p then 1 else 0

/-- The diagonal projection onto the coordinates other than `i, j`. -/
def compl : Matrix (Fin n) (Fin n) ℂ := 1 - (proj i j)ᵀ * proj i j

/-- The block embedding `𝔤𝔩_2(ℂ) → 𝔤𝔩_n(ℂ)` at rows and columns `i, j`. -/
def blockMat (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (proj i j)ᵀ * X * proj i j

/-- The block embedding of `GL_2` into `GL_n`, completed by the identity off `i, j`. -/
def blockUnit (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  blockMat i j M + compl i j

theorem proj_apply (p : Fin 2) (a : Fin n) :
    proj i j p a = if a = ![i, j] p then 1 else 0 := rfl

variable {i j}

theorem proj_mul_transpose (hij : i ≠ j) : proj i j * (proj i j)ᵀ = 1 := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, proj_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases p <;> fin_cases q <;> simp [Ne.symm hij, hij]

theorem proj_mul_transpose_mul (hij : i ≠ j) {m : Type*} (A : Matrix (Fin 2) m ℂ) :
    proj i j * ((proj i j)ᵀ * A) = A := by
  rw [← Matrix.mul_assoc, proj_mul_transpose hij, Matrix.one_mul]

theorem proj_mul_compl (hij : i ≠ j) : proj i j * compl i j = 0 := by
  rw [compl, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, proj_mul_transpose hij,
    Matrix.one_mul, sub_self]

theorem proj_mul_compl_mul (hij : i ≠ j) {m : Type*} (A : Matrix (Fin n) m ℂ) :
    proj i j * (compl i j * A) = 0 := by
  rw [← Matrix.mul_assoc, proj_mul_compl hij, Matrix.zero_mul]

theorem compl_mul_transpose (hij : i ≠ j) : compl i j * (proj i j)ᵀ = 0 := by
  rw [compl, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, proj_mul_transpose hij,
    Matrix.mul_one, sub_self]

theorem compl_mul_transpose_mul (hij : i ≠ j) {m : Type*} (A : Matrix (Fin 2) m ℂ) :
    compl i j * ((proj i j)ᵀ * A) = 0 := by
  rw [← Matrix.mul_assoc, compl_mul_transpose hij, Matrix.zero_mul]

theorem compl_mul_compl (hij : i ≠ j) : compl i j * compl i j = compl i j := by
  calc compl i j * compl i j = (1 - (proj i j)ᵀ * proj i j) * compl i j := rfl
    _ = compl i j := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, proj_mul_compl hij,
        Matrix.mul_zero, sub_zero]

theorem compl_mul_compl_mul (hij : i ≠ j) {m : Type*} (A : Matrix (Fin n) m ℂ) :
    compl i j * (compl i j * A) = compl i j * A := by
  rw [← Matrix.mul_assoc, compl_mul_compl hij]

theorem blockMat_mul (hij : i ≠ j) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    blockMat i j (X * Y) = blockMat i j X * blockMat i j Y := by
  simp only [blockMat, Matrix.mul_assoc, proj_mul_transpose_mul hij]

theorem blockUnit_mul (hij : i ≠ j) (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    blockUnit i j (M * N) = blockUnit i j M * blockUnit i j N := by
  simp only [blockUnit, blockMat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    proj_mul_transpose_mul hij, proj_mul_compl hij, compl_mul_transpose_mul hij,
    compl_mul_compl hij, Matrix.mul_zero, add_zero, zero_add]

theorem blockUnit_one : blockUnit i j 1 = 1 := by
  simp [blockUnit, blockMat, compl]

theorem blockUnit_mul_blockMat (hij : i ≠ j) (M X : Matrix (Fin 2) (Fin 2) ℂ) :
    blockUnit i j M * blockMat i j X = blockMat i j (M * X) := by
  simp only [blockUnit, blockMat, Matrix.add_mul, Matrix.mul_assoc,
    proj_mul_transpose_mul hij, compl_mul_transpose_mul hij, add_zero]

theorem blockMat_mul_blockUnit (hij : i ≠ j) (X M : Matrix (Fin 2) (Fin 2) ℂ) :
    blockMat i j X * blockUnit i j M = blockMat i j (X * M) := by
  simp only [blockUnit, blockMat, Matrix.mul_add, Matrix.mul_assoc,
    proj_mul_transpose_mul hij, proj_mul_compl hij, Matrix.mul_zero, add_zero]

theorem conjTranspose_proj : (proj i j)ᴴ = (proj i j)ᵀ := by
  ext a p
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, proj_apply]
  split_ifs <;> simp

theorem conjTranspose_transpose_proj : ((proj i j)ᵀ)ᴴ = proj i j := by
  ext p a
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, proj_apply]
  split_ifs <;> simp

theorem star_blockMat (X : Matrix (Fin 2) (Fin 2) ℂ) :
    star (blockMat i j X) = blockMat i j (star X) := by
  simp only [blockMat, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    conjTranspose_proj, conjTranspose_transpose_proj, Matrix.mul_assoc]

theorem star_compl : star (compl i j) = compl i j := by
  simp only [compl, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_mul, conjTranspose_proj,
    conjTranspose_transpose_proj]

theorem star_blockUnit (M : Matrix (Fin 2) (Fin 2) ℂ) :
    star (blockUnit i j M) = blockUnit i j (star M) := by
  rw [blockUnit, star_add, star_blockMat, star_compl, blockUnit]

theorem compl_apply_of_ne {a b : Fin n} (hab : a ≠ b) : compl i j a b = 0 := by
  simp only [compl, Matrix.sub_apply, Matrix.one_apply_ne hab, Matrix.mul_apply,
    Matrix.transpose_apply, proj_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_sub, neg_eq_zero]
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases ha' : a = j <;>
    by_cases hb' : b = j <;> simp_all

theorem blockMat_support (X : Matrix (Fin 2) (Fin 2) ℂ) {a b : Fin n}
    (h : blockMat i j X a b ≠ 0) : (a = i ∨ a = j) ∧ (b = i ∨ b = j) := by
  by_contra hc
  apply h
  rcases not_and_or.mp hc with ha | hb
  · push Not at ha
    simp [blockMat, Matrix.mul_apply, proj_apply, Fin.sum_univ_two, ha.1, ha.2]
  · push Not at hb
    simp [blockMat, Matrix.mul_apply, proj_apply, Fin.sum_univ_two, hb.1, hb.2]

theorem blockMat_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin n) :
    blockMat i j X a b = ∑ p : Fin 2, ∑ q : Fin 2,
      (if a = ![i, j] p then 1 else 0) * X p q * (if b = ![i, j] q then 1 else 0) := by
  simp only [blockMat, Matrix.mul_apply, Matrix.transpose_apply, proj_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem blockMat_single (p q : Fin 2) (c : ℂ) :
    blockMat i j (Matrix.single p q c) = Matrix.single (![i, j] p) (![i, j] q) c := by
  ext a b
  rw [blockMat_apply]
  simp only [Matrix.single_apply, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul]
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · by_cases ha : a = ![i, j] p <;> by_cases hb : b = ![i, j] q <;> simp [ha, hb, eq_comm]
  · intro q' _ hq'; simp [Ne.symm hq']
  · simp
  · intro p' _ hp'
    refine Finset.sum_eq_zero fun q' _ => ?_
    simp [Ne.symm hp']
  · simp

end Block

/-! ## Block-diagonal support and the nilradical of the parabolic -/

section Support

variable {n : ℕ} (i j : Fin n)

/-- Support in the diagonal and the `{i, j} × {i, j}` block. -/
def IsBlockDiag (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ a b : Fin n, g a b ≠ 0 → a = b ∨ ((a = i ∨ a = j) ∧ (b = i ∨ b = j))

/-- The nilradical `𝔫_P` of the parabolic with Levi block `{i, j}`: strictly upper triangular
matrices with vanishing `(i, j)` entry. -/
def InNP (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ a b : Fin n, ((b : ℕ) ≤ a ∨ (a = i ∧ b = j)) → X a b = 0

variable {i j}

theorem isBlockDiag_one : IsBlockDiag i j (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro a b h
  by_contra hc
  exact h (Matrix.one_apply_ne fun hab => hc (Or.inl hab))

theorem isBlockDiag_blockMat (X : Matrix (Fin 2) (Fin 2) ℂ) :
    IsBlockDiag i j (blockMat i j X) :=
  fun _ _ h => Or.inr (blockMat_support X h)

theorem isBlockDiag_blockUnit (M : Matrix (Fin 2) (Fin 2) ℂ) :
    IsBlockDiag i j (blockUnit i j M) := by
  intro a b h
  by_cases hab : a = b
  · exact Or.inl hab
  · right
    apply blockMat_support M
    intro h'
    apply h
    rw [blockUnit, Matrix.add_apply, compl_apply_of_ne hab, add_zero, h']

theorem InNP.sub {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : InNP i j X) (hY : InNP i j Y) :
    InNP i j (X - Y) := by
  intro a b h
  rw [Matrix.sub_apply, hX a b h, hY a b h, sub_zero]

theorem InNP.strict {X : Matrix (Fin n) (Fin n) ℂ} (hX : InNP i j X) :
    ∀ a b : Fin n, (b : ℕ) ≤ a → X a b = 0 :=
  fun a b h => hX a b (Or.inl h)

theorem inNP_mul (hj : (j : ℕ) = i + 1) {g h X : Matrix (Fin n) (Fin n) ℂ}
    (hg : IsBlockDiag i j g) (hh : IsBlockDiag i j h) (hX : InNP i j X) :
    InNP i j (g * X * h) := by
  intro a d had
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h1 : g a b = 0
  · simp [h1]
  by_cases h3 : h c d = 0
  · simp [h3]
  rw [hX b c ?_, mul_zero, zero_mul]
  have e1 := hg a b h1
  have e2 := hh c d h3
  simp only [Fin.ext_iff] at e1 e2 had ⊢
  omega

end Support

/-! ## Commutation with the diagonal directions off the block -/

section Commute

variable {n : ℕ} {i j : Fin n} {k : Fin n}

theorem proj_mul_single (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ) :
    proj i j * Matrix.single k k c = 0 := by
  ext p b
  by_cases hb : b = k
  · subst hb
    rw [Matrix.mul_single_apply_same, proj_apply, Matrix.zero_apply]
    fin_cases p <;> simp [hki, hkj]
  · rw [Matrix.mul_single_apply_of_ne c k k p b hb, Matrix.zero_apply]

theorem single_mul_transpose (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ) :
    Matrix.single k k c * (proj i j)ᵀ = 0 := by
  ext a q
  by_cases ha : a = k
  · subst ha
    rw [Matrix.single_mul_apply_same, Matrix.transpose_apply, proj_apply, Matrix.zero_apply]
    fin_cases q <;> simp [hki, hkj]
  · rw [Matrix.single_mul_apply_of_ne c k k a q ha, Matrix.zero_apply]

theorem blockMat_mul_single (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ)
    (Y : Matrix (Fin 2) (Fin 2) ℂ) : blockMat i j Y * Matrix.single k k c = 0 := by
  rw [blockMat, Matrix.mul_assoc, proj_mul_single hki hkj, Matrix.mul_zero]

theorem single_mul_blockMat (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ)
    (Y : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.single k k c * blockMat i j Y = 0 := by
  rw [blockMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, single_mul_transpose hki hkj,
    Matrix.zero_mul, Matrix.zero_mul]

theorem compl_mul_single (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ) :
    compl i j * Matrix.single k k c = Matrix.single k k c := by
  rw [compl, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, proj_mul_single hki hkj,
    Matrix.mul_zero, sub_zero]

theorem single_mul_compl (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ) :
    Matrix.single k k c * compl i j = Matrix.single k k c := by
  rw [compl, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, single_mul_transpose hki hkj,
    Matrix.zero_mul, sub_zero]

theorem blockUnit_mul_single (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    blockUnit i j M * Matrix.single k k c = Matrix.single k k c := by
  rw [blockUnit, Matrix.add_mul, blockMat_mul_single hki hkj, compl_mul_single hki hkj, zero_add]

theorem single_mul_blockUnit (hki : k ≠ i) (hkj : k ≠ j) (c : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.single k k c * blockUnit i j M = Matrix.single k k c := by
  rw [blockUnit, Matrix.mul_add, single_mul_blockMat hki hkj, single_mul_compl hki hkj, zero_add]

end Commute

/-! ## The embeddings `U(2) → U(n)` and `ℂ ⊗ 𝔤𝔩_2(ℂ) → ℂ ⊗ 𝔤𝔩_n(ℂ)` -/

section Embedding

variable {n : ℕ} (i j : Fin n)

theorem blockMat_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    blockMat i j (X + Y) = blockMat i j X + blockMat i j Y := by
  simp only [blockMat, Matrix.mul_add, Matrix.add_mul]

theorem blockMat_sub (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    blockMat i j (X - Y) = blockMat i j X - blockMat i j Y := by
  simp only [blockMat, Matrix.mul_sub, Matrix.sub_mul]

/-- The block embedding as an `ℝ`-linear map. -/
def blockLin : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := blockMat i j
  map_add' := blockMat_add i j
  map_smul' r X := by
    simp only [blockMat, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

variable {i j}

/-- The complexified block embedding `ℂ ⊗_ℝ 𝔤𝔩_2(ℂ) → ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`, a Lie algebra map. -/
def blockLie (hij : i ≠ j) :
    (ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ) →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  { LinearMap.baseChange ℂ (blockLin i j) with
    map_lie' := by
      intro x y
      induction x using TensorProduct.inductionOn with
      | tmul c X =>
        induction y using TensorProduct.inductionOn with
        | tmul d Y =>
          simp only [LinearMap.toFun_eq_coe, LieAlgebra.ExtendScalars.bracket_tmul,
            LinearMap.baseChange_tmul]
          congr 1
          change blockMat i j ⁅X, Y⁆ = ⁅blockMat i j X, blockMat i j Y⁆
          rw [Ring.lie_def, Ring.lie_def, blockMat_sub, blockMat_mul hij, blockMat_mul hij]
        | add y₁ y₂ h₁ h₂ =>
          simp only [LinearMap.toFun_eq_coe] at h₁ h₂ ⊢
          rw [lie_add, map_add, h₁, h₂, map_add, lie_add]
      | add x₁ x₂ h₁ h₂ =>
        simp only [LinearMap.toFun_eq_coe] at h₁ h₂ ⊢
        rw [add_lie, map_add, h₁, h₂, map_add, add_lie] }

theorem blockLie_tmul (hij : i ≠ j) (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    blockLie hij (c ⊗ₜ X) = c ⊗ₜ blockMat i j X := rfl

theorem blockUnit_mem (hij : i ≠ j) (M : Matrix.unitaryGroup (Fin 2) ℂ) :
    blockUnit i j (M : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_blockUnit, ← blockUnit_mul hij,
    Unitary.mul_star_self_of_mem M.2, blockUnit_one]

/-- The block embedding `U(2) → U(n)`. -/
def blockUnitHom (hij : i ≠ j) :
    Matrix.unitaryGroup (Fin 2) ℂ →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun M := ⟨blockUnit i j M, blockUnit_mem hij M⟩
  map_one' := Subtype.ext blockUnit_one
  map_mul' M N := Subtype.ext (blockUnit_mul hij M N)

theorem coe_blockUnitHom (hij : i ≠ j) (M : Matrix.unitaryGroup (Fin 2) ℂ) :
    ((blockUnitHom hij M : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      blockUnit i j M := rfl

theorem continuous_blockUnit :
    Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => blockUnit i j M :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).add continuous_const

theorem continuous_blockUnitHom (hij : i ≠ j) : Continuous (blockUnitHom (n := n) hij) :=
  Continuous.subtype_mk (continuous_blockUnit.comp continuous_subtype_val) _

end Embedding

/-! ## Quotients of representations and of Lie algebra actions -/

section Quotient

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The action of `L` on `V ⧸ S` induced by an action preserving `S`. -/
def quotLieHom {L : Type*} [LieRing L] [LieAlgebra ℂ L] (S : Submodule ℂ V)
    (φ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (h : ∀ x, ∀ v ∈ S, φ x v ∈ S) :
    L →ₗ⁅ℂ⁆ Module.End ℂ (V ⧸ S) where
  toFun x := S.mapQ S (φ x) (fun v hv => h x v hv)
  map_add' x y := by
    apply Submodule.linearMap_qext
    ext v
    simp [Submodule.mapQ_apply]
  map_smul' c x := by
    apply Submodule.linearMap_qext
    ext v
    simp [Submodule.mapQ_apply]
  map_lie' := by
    intro x y
    apply Submodule.linearMap_qext
    ext v
    simp [Submodule.mapQ_apply, Ring.lie_def]

theorem quotLieHom_mk {L : Type*} [LieRing L] [LieAlgebra ℂ L] (S : Submodule ℂ V)
    (φ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (h : ∀ x, ∀ v ∈ S, φ x v ∈ S) (x : L) (v : V) :
    quotLieHom S φ h x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ x v) := rfl

/-- The representation on `V ⧸ S` induced by a representation preserving `S`. -/
def quotRep {G : Type*} [Monoid G] (S : Submodule ℂ V) (ρ : Representation ℂ G V)
    (h : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : Representation ℂ G (V ⧸ S) where
  toFun g := S.mapQ S (ρ g) (fun v hv => h g v hv)
  map_one' := by
    apply Submodule.linearMap_qext
    ext v
    simp [Submodule.mapQ_apply]
  map_mul' g g' := by
    apply Submodule.linearMap_qext
    ext v
    simp [Submodule.mapQ_apply]

theorem quotRep_mk {G : Type*} [Monoid G] (S : Submodule ℂ V) (ρ : Representation ℂ G V)
    (h : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) (v : V) :
    quotRep S ρ h g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl

end Quotient

/-! ## The subspace `S` cut out off the block -/

section Sub

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (i j : Fin n) (a b : Fin n → ℂ)

theorem ne_of_adj {i j : Fin n} (hj : (j : ℕ) = i + 1) : i ≠ j := by
  intro h
  subst h
  omega

/-- `(c, α)` is a diagonal direction `c E_kk` with its prescribed eigenvalue: `(1, a_k)` or
`(i, b_k)`. -/
def IsDiagEigen (k : Fin n) (c α : ℂ) : Prop :=
  (c = 1 ∧ α = a k) ∨ (c = Complex.I ∧ α = b k)

/-- Generators of `S`: the vectors `π(1 ⊗ X) v` for `X ∈ 𝔫_P`, and `π(1 ⊗ c E_kk) v - α v` for
`k ∉ {i, j}` and `(c, α)` a diagonal direction with its eigenvalue. -/
def offGens : Set V :=
  {w | ∃ (X : Matrix (Fin n) (Fin n) ℂ) (v : V), InNP i j X ∧ π (1 ⊗ₜ X) v = w} ∪
  {w | ∃ (k : Fin n) (c α : ℂ) (v : V), k ≠ i ∧ k ≠ j ∧ IsDiagEigen a b k c α ∧
    π (1 ⊗ₜ Matrix.single k k c) v - α • v = w}

/-- The subspace `S = 𝔫_P V + ∑_{k ∉ {i, j}} (im (E_kk - a_k) + im (i E_kk - b_k))`. -/
def offSub : Submodule ℂ V := Submodule.span ℂ (offGens π i j a b)

variable {π i j a b}

theorem inNP_mem {X : Matrix (Fin n) (Fin n) ℂ} (hX : InNP i j X) (v : V) :
    π (1 ⊗ₜ X) v ∈ offSub π i j a b :=
  Submodule.subset_span (Or.inl ⟨X, v, hX, rfl⟩)

theorem diag_mem {k : Fin n} {c α : ℂ} (hki : k ≠ i) (hkj : k ≠ j)
    (h : IsDiagEigen a b k c α) (v : V) :
    π (1 ⊗ₜ Matrix.single k k c) v - α • v ∈ offSub π i j a b :=
  Submodule.subset_span (Or.inr ⟨k, c, α, v, hki, hkj, h, rfl⟩)

theorem offSub_stable (f : V →ₗ[ℂ] V)
    (h : ∀ w ∈ offGens π i j a b, f w ∈ offSub π i j a b) :
    ∀ v ∈ offSub π i j a b, f v ∈ offSub π i j a b := by
  have : offSub π i j a b ≤ (offSub π i j a b).comap f := Submodule.span_le.mpr h
  exact fun v hv => this hv

theorem offSub_stable_pi (hj : (j : ℕ) = i + 1) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : IsBlockDiag i j Z)
    (hZc : ∀ k : Fin n, k ≠ i → k ≠ j → ∀ c : ℂ,
      Z * Matrix.single k k c = Matrix.single k k c * Z) :
    ∀ v ∈ offSub π i j a b, π (1 ⊗ₜ Z) v ∈ offSub π i j a b := by
  apply offSub_stable
  rintro w (⟨X, v, hX, rfl⟩ | ⟨k, c, α, v, hki, hkj, hk, rfl⟩)
  · have h := LinearMap.congr_fun (complex_map_commutator π Z X) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have h' : π (1 ⊗ₜ Z) (π (1 ⊗ₜ X) v) =
        π (1 ⊗ₜ (Z * X - X * Z)) v + π (1 ⊗ₜ X) (π (1 ⊗ₜ Z) v) := by
      rw [h]; abel
    rw [h']
    refine Submodule.add_mem _ (inNP_mem ?_ v) (inNP_mem hX _)
    have e1 := inNP_mul hj hZ isBlockDiag_one hX
    have e2 := inNP_mul hj isBlockDiag_one hZ hX
    rw [Matrix.mul_one] at e1
    rw [Matrix.one_mul] at e2
    exact e1.sub e2
  · have h := LinearMap.congr_fun (complex_map_commutator π Z (Matrix.single k k c)) v
    rw [hZc k hki hkj c, sub_self, TensorProduct.tmul_zero, map_zero] at h
    simp only [LinearMap.zero_apply, LinearMap.sub_apply, Module.End.mul_apply] at h
    have h' : π (1 ⊗ₜ Z) (π (1 ⊗ₜ Matrix.single k k c) v) =
        π (1 ⊗ₜ Matrix.single k k c) (π (1 ⊗ₜ Z) v) := sub_eq_zero.mp h.symm
    rw [map_sub, map_smul, h']
    exact diag_mem hki hkj hk _

theorem offSub_stable_blockLie (hj : (j : ℕ) = i + 1)
    (x : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ v ∈ offSub π i j a b, π (blockLie (ne_of_adj hj) x) v ∈ offSub π i j a b := by
  induction x using TensorProduct.inductionOn with
  | tmul c Y =>
    intro v hv
    have e : (c ⊗ₜ[ℝ] blockMat i j Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) =
        c • ((1 : ℂ) ⊗ₜ[ℝ] blockMat i j Y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [blockLie_tmul, e, map_smul, LinearMap.smul_apply]
    refine Submodule.smul_mem _ c (offSub_stable_pi hj (isBlockDiag_blockMat Y) ?_ v hv)
    intro k hki hkj c'
    rw [blockMat_mul_single hki hkj, single_mul_blockMat hki hkj]
  | add x y hx hy =>
    intro v hv
    rw [map_add, map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (hx v hv) (hy v hv)

theorem offSub_stable_rho (hj : (j : ℕ) = i + 1)
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V} (hGK : IsComplexGKModule n ρ π)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∀ v ∈ offSub π i j a b, ρ (blockUnitHom (ne_of_adj hj) g) v ∈ offSub π i j a b := by
  apply offSub_stable
  set u := blockUnitHom (ne_of_adj hj) g with hu_def
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) = blockUnit i j g := rfl
  have hus : star (u : Matrix (Fin n) (Fin n) ℂ) =
      blockUnit i j (star (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [hu, star_blockUnit]
  rintro w (⟨X, v, hX, rfl⟩ | ⟨k, c, α, v, hki, hkj, hk, rfl⟩)
  · rw [hGK.2.2.2 u X v]
    apply inNP_mem
    rw [hus, hu]
    exact inNP_mul hj (isBlockDiag_blockUnit _) (isBlockDiag_blockUnit _) hX
  · rw [map_sub, map_smul, hGK.2.2.2 u _ v]
    have e : (u : Matrix (Fin n) (Fin n) ℂ) * Matrix.single k k c *
        star (u : Matrix (Fin n) (Fin n) ℂ) = Matrix.single k k c := by
      rw [hus, hu, blockUnit_mul_single hki hkj, single_mul_blockUnit hki hkj]
    rw [e]
    exact diag_mem hki hkj hk _

theorem offSub_le_ker {ℓ : V →ₗ[ℂ] ℂ} (hℓ : IsComplexJacquetFunctional n π ℓ a b) :
    offSub π i j a b ≤ LinearMap.ker ℓ := by
  apply Submodule.span_le.mpr
  rintro w (⟨X, v, hX, rfl⟩ | ⟨k, c, α, v, hki, hkj, hk, rfl⟩)
  · rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hℓ.1 X hX.strict v
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(hℓ.2 k v).1, sub_self]
    · rw [(hℓ.2 k v).2, sub_self]

end Sub

/-! ## The `(𝔤𝔩_2(ℂ), U(2))`-module `V ⧸ S` -/

section Module

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (i j : Fin n) (a b : Fin n → ℂ)

/-- The `U(2)`-representation on `V ⧸ S` through the block embedding `U(2) → U(n)`. -/
def blockRho (hGK : IsComplexGKModule n ρ π) (hj : (j : ℕ) = i + 1) :
    Representation ℂ (Matrix.unitaryGroup (Fin 2) ℂ) (V ⧸ offSub π i j a b) :=
  quotRep _ (ρ.comp (blockUnitHom (ne_of_adj hj)))
    (fun g v hv => offSub_stable_rho hj hGK g v hv)

/-- The `ℂ ⊗_ℝ 𝔤𝔩_2(ℂ)`-action on `V ⧸ S` through the block embedding. -/
def blockPi (hj : (j : ℕ) = i + 1) :
    (ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (V ⧸ offSub π i j a b) :=
  quotLieHom _ (π.comp (blockLie (ne_of_adj hj)))
    (fun x v hv => offSub_stable_blockLie hj x v hv)

variable {ρ π i j a b}

theorem blockRho_mk (hGK : IsComplexGKModule n ρ π) (hj : (j : ℕ) = i + 1)
    (g : Matrix.unitaryGroup (Fin 2) ℂ) (v : V) :
    blockRho ρ π i j a b hGK hj g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (ρ (blockUnitHom (ne_of_adj hj) g) v) := rfl

theorem blockPi_mk (hj : (j : ℕ) = i + 1) (X : Matrix (Fin 2) (Fin 2) ℂ) (v : V) :
    blockPi π i j a b hj (1 ⊗ₜ X) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (1 ⊗ₜ blockMat i j X) v) := rfl

theorem hasDerivAt_blockUnit (γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hγ : ∀ p q, HasDerivAt (fun t => γ t p q) (X p q) 0) (p q : Fin n) :
    HasDerivAt (fun t => blockUnit i j (γ t) p q) (blockMat i j X p q) 0 := by
  have h : HasDerivAt (fun t => (∑ r : Fin 2, ∑ s : Fin 2,
      (if p = ![i, j] r then 1 else 0) * γ t r s * (if q = ![i, j] s then 1 else 0)) +
        compl i j p q)
      (∑ r : Fin 2, ∑ s : Fin 2,
        (if p = ![i, j] r then 1 else 0) * X r s * (if q = ![i, j] s then 1 else 0)) 0 :=
    HasDerivAt.add_const _ (HasDerivAt.fun_sum fun r _ => HasDerivAt.fun_sum fun s _ =>
      ((hγ r s).const_mul _).mul_const _)
  simpa only [blockUnit, Matrix.add_apply, blockMat_apply] using h

theorem isComplexGKModule_block (hGK : IsComplexGKModule n ρ π) (hj : (j : ℕ) = i + 1) :
    IsComplexGKModule 2 (blockRho ρ π i j a b hGK hj) (blockPi π i j a b hj) := by
  have hij := ne_of_adj hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have : Module.Finite ℂ (FiniteVectors.orbitSpan ρ v) := hGK.1 v
    show Module.Finite ℂ (FiniteVectors.orbitSpan _ _)
    refine Submodule.finiteDimensional_of_le
      (S₂ := (FiniteVectors.orbitSpan ρ v).map (offSub π i j a b).mkQ) ?_
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact ⟨ρ (blockUnitHom hij g) v, FiniteVectors.action_mem_orbitSpan ρ _ v, rfl⟩
  · intro w ℓ
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact (hGK.2.1 v (ℓ ∘ₗ (offSub π i j a b).mkQ)).comp (continuous_blockUnitHom hij)
  · intro γ X hγ0 hγ w ℓ
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have h0 : blockUnitHom hij (γ 0) = 1 := by rw [hγ0, map_one]
    exact hGK.2.2.1 (fun t => blockUnitHom hij (γ t)) (blockMat i j X) h0
      (hasDerivAt_blockUnit (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)) X hγ) v
      (ℓ ∘ₗ (offSub π i j a b).mkQ)
  · intro g X w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [blockPi_mk, blockRho_mk, blockRho_mk, blockPi_mk, hGK.2.2.2]
    have e : ((blockUnitHom hij g : Matrix.unitaryGroup (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * blockMat i j X *
        star ((blockUnitHom hij g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        blockMat i j ((g : Matrix (Fin 2) (Fin 2) ℂ) * X * star (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [coe_blockUnitHom, star_blockUnit, blockUnit_mul_blockMat hij,
        blockMat_mul_blockUnit hij]
    rw [e]

theorem eq_single_of_strict (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : ∀ p q : Fin 2, (q : ℕ) ≤ p → X p q = 0) : X = Matrix.single 0 1 (X 0 1) := by
  ext p q
  fin_cases p <;> fin_cases q <;> simp <;> exact hX _ _ (by simp)

theorem single_strict (hj : (j : ℕ) = i + 1) (c : ℂ) :
    ∀ p q : Fin n, (q : ℕ) ≤ p → Matrix.single i j c p q = 0 := by
  intro p q hpq
  rw [Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    omega
  · rfl

theorem isJacquet_block (hj : (j : ℕ) = i + 1)
    {ℓ : V →ₗ[ℂ] ℂ} (hℓ : IsComplexJacquetFunctional n π ℓ a b) :
    IsComplexJacquetFunctional 2 (blockPi π i j a b hj)
      ((offSub π i j a b).liftQ ℓ (offSub_le_ker hℓ)) ![a i, a j] ![b i, b j] := by
  refine ⟨?_, ?_⟩
  · intro X hX w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [blockPi_mk, Submodule.liftQ_apply, eq_single_of_strict X hX, blockMat_single]
    exact hℓ.1 _ (single_strict hj _) v
  · intro p w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [blockPi_mk, blockPi_mk, Submodule.liftQ_apply, Submodule.liftQ_apply,
      Submodule.liftQ_apply, blockMat_single, blockMat_single]
    have ha : ![a i, a j] p = a (![i, j] p) := by fin_cases p <;> rfl
    have hb : ![b i, b j] p = b (![i, j] p) := by fin_cases p <;> rfl
    rw [ha, hb]
    exact hℓ.2 _ v

end Module

/-! ## The reduction -/

/-- Reduction of the rank-one reordering to `GL_2(ℂ)`: the ordering statement for
`(𝔤𝔩_2(ℂ), U(2))`-modules implies the rank-one reordering for `(𝔤𝔩_n(ℂ), U(n))`-modules. -/
theorem complexJacquetRankOne_of_glTwo (hT : ComplexGLTwoJacquetOrderingStatement.{uV}) :
    ComplexJacquetRankOneStatement.{uV} := by
  intro n V _ _ ρ π hGK _ _ ℓ a b hℓ0 hℓ i j hj _
  have hij := ne_of_adj hj
  set S := offSub π i j a b with hS
  have hlift : S.liftQ ℓ (offSub_le_ker hℓ) ≠ 0 := by
    intro h
    apply hℓ0
    rw [← S.liftQ_mkQ ℓ (offSub_le_ker hℓ), h, LinearMap.zero_comp]
  obtain ⟨μ, a'', b'', hμ0, hμ, hsum, hord⟩ :=
    hT (V ⧸ S) (blockRho ρ π i j a b hGK hj) (blockPi π i j a b hj)
      (isComplexGKModule_block hGK hj) (S.liftQ ℓ (offSub_le_ker hℓ)) ![a i, a j] ![b i, b j]
      hlift (isJacquet_block hj hℓ)
  refine ⟨μ ∘ₗ S.mkQ, fun k => if k = i then a'' 0 else if k = j then a'' 1 else a k,
    fun k => if k = i then b'' 0 else if k = j then b'' 1 else b k, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hμ0
    apply Submodule.linearMap_qext
    rw [h, LinearMap.zero_comp]
  · refine ⟨?_, ?_⟩
    · intro X hX v
      have hsplit : X = (X - Matrix.single i j (X i j)) +
          blockMat i j (Matrix.single 0 1 (X i j)) := by
        rw [blockMat_single]
        simp
      have hN : InNP i j (X - Matrix.single i j (X i j)) := by
        intro p q hpq
        rw [Matrix.sub_apply]
        rcases hpq with h | ⟨rfl, rfl⟩
        · rw [hX p q h, single_strict hj _ p q h, sub_zero]
        · rw [Matrix.single_apply_same, sub_self]
      rw [hsplit, TensorProduct.tmul_add, map_add, LinearMap.add_apply, map_add,
        LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero S).mpr (inNP_mem hN v), map_zero, zero_add,
        ← blockPi_mk hj]
      exact hμ.1 _ (single_strict (i := (0 : Fin 2)) (j := 1) rfl _) _
    · intro k v
      have hblock : ∀ (p : Fin 2) (c : ℂ),
          (μ ∘ₗ S.mkQ) (π (1 ⊗ₜ Matrix.single (![i, j] p) (![i, j] p) c) v) =
            μ (blockPi π i j a b hj (1 ⊗ₜ Matrix.single p p c) (Submodule.Quotient.mk v)) := by
        intro p c
        rw [blockPi_mk, blockMat_single]
        rfl
      by_cases hki : k = i
      · rw [hki]
        have h0 := hblock 0
        simp only [Matrix.cons_val_zero] at h0
        rw [h0, h0, (hμ.2 0 _).1, (hμ.2 0 _).2]
        simp
      · by_cases hkj : k = j
        · rw [hkj]
          have h1 := hblock 1
          simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
          rw [h1, h1, (hμ.2 1 _).1, (hμ.2 1 _).2]
          simp [Ne.symm hij]
        · have e1 : S.mkQ (π (1 ⊗ₜ Matrix.single k k 1) v) = a k • S.mkQ v := by
            rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
            exact diag_mem hki hkj (Or.inl ⟨rfl, rfl⟩) v
          have e2 : S.mkQ (π (1 ⊗ₜ Matrix.single k k Complex.I) v) = b k • S.mkQ v := by
            rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
            exact diag_mem hki hkj (Or.inr ⟨rfl, rfl⟩) v
          simp only [LinearMap.comp_apply, e1, e2, map_smul, smul_eq_mul, hki, hkj, ↓reduceIte]
          exact ⟨trivial, trivial⟩
  · intro k hki hkj
    simp [hki, hkj]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hsum
    simpa [Ne.symm hij] using hsum
  · simpa [Ne.symm hij] using hord

end RankOneBlock

/-- The rank-one reordering of Jacquet exponents for `(𝔤𝔩_n(ℂ), U(n))`-modules follows from the
ordering statement for `(𝔤𝔩_2(ℂ), U(2))`-modules. -/
def ComplexJacquetRankOneReductionStatement : Prop :=
  ComplexGLTwoJacquetOrderingStatement.{uV} → ComplexJacquetRankOneStatement.{uV}

theorem complexJacquetRankOneReduction : ComplexJacquetRankOneReductionStatement.{uV} :=
  RankOneBlock.complexJacquetRankOne_of_glTwo

end Langlands.Archimedean
