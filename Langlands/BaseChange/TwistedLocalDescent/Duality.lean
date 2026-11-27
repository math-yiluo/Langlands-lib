import Langlands.BaseChange.RelativeParabolicDiscriminant
import Langlands.BaseChange.TwistedLocalDescent.PairingDeterminant
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-! # The twisted discriminant on the opposite nilradical

For a standard block Levi element `m` and an automorphism `σ` of a finite separable extension
`E/F`, the twisted relative discriminant `D_{G/M,σ}(m)` is the product of the determinant of
`σ − Ad(m)⁻¹` on the strictly block lower matrices `𝔲̄` and of `σ⁻¹ − Ad(m)` on `𝔲̄`
(trace duality between `𝔤/𝔭̄` and `𝔲̄`). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear Module

universe u v

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] {n : ℕ} (B : BlockShape n)

/-- The strictly block lower matrices `𝔲̄(E)`: entries vanish unless the row block is larger
than the column block. -/
def lowerLie : Submodule E (Matrix (Fin n) (Fin n) E) where
  carrier := {X | ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → X a b = 0}
  add_mem' {X Y} hX hY a b h := by
    simp only [Matrix.add_apply, hX a b h, hY a b h, add_zero]
  zero_mem' _ _ _ := rfl
  smul_mem' c X hX a b h := by
    simp only [Matrix.smul_apply, hX a b h, smul_zero]

/-- The block lower triangular matrices `𝔭̄(E)`. -/
def lowerParabolicLie : Submodule E (Matrix (Fin n) (Fin n) E) where
  carrier := {X | ∀ a b, B.coordinateBlock a < B.coordinateBlock b → X a b = 0}
  add_mem' {X Y} hX hY a b h := by
    simp only [Matrix.add_apply, hX a b h, hY a b h, add_zero]
  zero_mem' _ _ _ := rfl
  smul_mem' c X hX a b h := by
    simp only [Matrix.smul_apply, hX a b h, smul_zero]

theorem mem_lowerLie (X : Matrix (Fin n) (Fin n) E) :
    X ∈ lowerLie B ↔ ∀ a b, B.coordinateBlock a ≤ B.coordinateBlock b → X a b = 0 := Iff.rfl

theorem mem_lowerParabolicLie (X : Matrix (Fin n) (Fin n) E) :
    X ∈ lowerParabolicLie B ↔
      ∀ a b, B.coordinateBlock a < B.coordinateBlock b → X a b = 0 := Iff.rfl

theorem blockDiagonalLieSubmodule_le_lowerParabolicLie :
    blockDiagonalLieSubmodule B E ≤ lowerParabolicLie B := by
  intro X hX a b h
  exact (mem_blockDiagonalLieSubmodule B E X).mp hX a b h.ne

theorem lowerLie_le_lowerParabolicLie : lowerLie B ≤ lowerParabolicLie (E := E) B :=
  fun _ hX a b h => hX a b h.le

/-- A matrix is block diagonal plus strictly block lower exactly when it is block lower. -/
theorem lowerParabolicLie_eq_sup :
    lowerParabolicLie B = blockDiagonalLieSubmodule B E ⊔ lowerLie B := by
  apply le_antisymm
  · intro X hX
    let D : Matrix (Fin n) (Fin n) E := Matrix.of fun a b =>
      if B.coordinateBlock a = B.coordinateBlock b then X a b else 0
    let L : Matrix (Fin n) (Fin n) E := Matrix.of fun a b =>
      if B.coordinateBlock b < B.coordinateBlock a then X a b else 0
    have hD : D ∈ blockDiagonalLieSubmodule B E := by
      rw [mem_blockDiagonalLieSubmodule]
      intro a b hab
      simp [D, hab]
    have hL : L ∈ lowerLie B := by
      intro a b hab
      simp [L, not_lt.mpr hab]
    have hX' : X = D + L := by
      ext a b
      simp only [Matrix.add_apply, D, L, Matrix.of_apply]
      rcases lt_trichotomy (B.coordinateBlock a) (B.coordinateBlock b) with h | h | h
      · rw [ite_eq_right h.ne, ite_eq_right (not_lt.mpr h.le), hX a b h, add_zero]
      · rw [ite_eq_left h, ite_eq_right (by rw [h]; exact lt_irrefl _), add_zero]
      · rw [ite_eq_right h.ne', ite_eq_left h, zero_add]
    rw [hX']
    exact Submodule.add_mem_sup hD hL
  · exact sup_le (blockDiagonalLieSubmodule_le_lowerParabolicLie B)
      (lowerLie_le_lowerParabolicLie B)

theorem disjoint_blockDiagonalLieSubmodule_lowerLie :
    Disjoint (blockDiagonalLieSubmodule B E) (lowerLie B) := by
  rw [Submodule.disjoint_def]
  intro X hD hL
  ext a b
  by_cases h : B.coordinateBlock a = B.coordinateBlock b
  · exact hL a b h.le
  · exact (mem_blockDiagonalLieSubmodule B E X).mp hD a b h

section Operators

/-- Left and right multiplication by a block diagonal matrix preserve block shapes. -/
theorem leviEmbedding_apply_eq_zero (m : B.Levi E) {a c : Fin n}
    (h : B.coordinateBlock a ≠ B.coordinateBlock c) : (B.leviEmbedding E m).val a c = 0 := by
  obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective c
  exact B.leviEmbedding_apply_ne E m x y (by simpa [BlockShape.coordinateBlock] using h)

/-- The value of `linearAdjoint` of a block diagonal element at a position depends only on the
entries of the same block pair. -/
theorem linearAdjoint_leviEmbedding_apply_eq_zero (m : B.Levi E) (X : Matrix (Fin n) (Fin n) E)
    {a b : Fin n} (hX : ∀ c d, B.coordinateBlock c = B.coordinateBlock a →
      B.coordinateBlock d = B.coordinateBlock b → X c d = 0) :
    linearAdjoint (B.leviEmbedding E m) X a b = 0 := by
  change ((B.leviEmbedding E m).val * (X * (B.leviEmbedding E m)⁻¹.val)) a b = 0
  rw [← map_inv]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro c _
  apply Finset.sum_eq_zero
  intro d _
  by_cases hc : B.coordinateBlock a = B.coordinateBlock c
  · by_cases hd : B.coordinateBlock d = B.coordinateBlock b
    · rw [hX c d hc.symm hd, zero_mul, mul_zero]
    · rw [leviEmbedding_apply_eq_zero B m⁻¹ hd, mul_zero, mul_zero]
  · rw [leviEmbedding_apply_eq_zero B m hc, zero_mul]

theorem linearAdjoint_mem_lowerLie (m : B.Levi E) {X : Matrix (Fin n) (Fin n) E}
    (hX : X ∈ lowerLie B) : linearAdjoint (B.leviEmbedding E m) X ∈ lowerLie B := by
  intro a b hab
  apply linearAdjoint_leviEmbedding_apply_eq_zero
  intro c d hc hd
  exact hX c d (by rw [hc, hd]; exact hab)

theorem linearAdjoint_mem_lowerParabolicLie (m : B.Levi E) {X : Matrix (Fin n) (Fin n) E}
    (hX : X ∈ lowerParabolicLie B) :
    linearAdjoint (B.leviEmbedding E m) X ∈ lowerParabolicLie B := by
  intro a b hab
  apply linearAdjoint_leviEmbedding_apply_eq_zero
  intro c d hc hd
  exact hX c d (by rw [hc, hd]; exact hab)

theorem linearAdjoint_mem_blockDiagonalLieSubmodule (m : B.Levi E)
    {X : Matrix (Fin n) (Fin n) E} (hX : X ∈ blockDiagonalLieSubmodule B E) :
    linearAdjoint (B.leviEmbedding E m) X ∈ blockDiagonalLieSubmodule B E := by
  rw [mem_blockDiagonalLieSubmodule] at hX ⊢
  intro a b hab
  apply linearAdjoint_leviEmbedding_apply_eq_zero
  intro c d hc hd
  exact hX c d (by rw [hc, hd]; exact hab)

variable (σ : E ≃ₐ[F] E)

/-- The entrywise action of `σ` on matrices, as an `F`-linear map. -/
def matrixSigma : Matrix (Fin n) (Fin n) E →ₗ[F] Matrix (Fin n) (Fin n) E :=
  σ.toLinearMap.mapMatrix

@[simp]
theorem matrixSigma_apply (X : Matrix (Fin n) (Fin n) E) (a b : Fin n) :
    matrixSigma (n := n) σ X a b = σ (X a b) := rfl

/-- The twisted operator `T = σ − Ad(m)⁻¹`, `X ↦ σ(X) − m⁻¹ X m`. -/
def twistedOperator (m : B.Levi E) : Module.End F (Matrix (Fin n) (Fin n) E) :=
  matrixSigma σ - (linearAdjoint (B.leviEmbedding E m⁻¹)).restrictScalars F

/-- The adjoint operator `T' = σ⁻¹ − Ad(m)`, `Y ↦ σ⁻¹(Y) − m Y m⁻¹`. -/
def twistedAdjointOperator (m : B.Levi E) : Module.End F (Matrix (Fin n) (Fin n) E) :=
  matrixSigma σ.symm - (linearAdjoint (B.leviEmbedding E m)).restrictScalars F

theorem matrixSigma_mem_lowerLie {X : Matrix (Fin n) (Fin n) E} (hX : X ∈ lowerLie B) :
    matrixSigma σ X ∈ lowerLie B := fun a b h => by
  rw [matrixSigma_apply, hX a b h, map_zero]

theorem matrixSigma_mem_lowerParabolicLie {X : Matrix (Fin n) (Fin n) E}
    (hX : X ∈ lowerParabolicLie B) : matrixSigma σ X ∈ lowerParabolicLie B := fun a b h => by
  rw [matrixSigma_apply, hX a b h, map_zero]

theorem matrixSigma_mem_blockDiagonalLieSubmodule {X : Matrix (Fin n) (Fin n) E}
    (hX : X ∈ blockDiagonalLieSubmodule B E) :
    matrixSigma σ X ∈ blockDiagonalLieSubmodule B E := by
  rw [mem_blockDiagonalLieSubmodule] at hX ⊢
  intro a b h
  rw [matrixSigma_apply, hX a b h, map_zero]

theorem twistedOperator_le_lowerLie (m : B.Levi E) :
    (lowerLie B).restrictScalars F ≤
      ((lowerLie B).restrictScalars F).comap (twistedOperator B σ m) := by
  intro X hX
  change matrixSigma σ X - linearAdjoint (B.leviEmbedding E m⁻¹) X ∈ lowerLie B
  exact sub_mem (matrixSigma_mem_lowerLie B σ hX)
    (linearAdjoint_mem_lowerLie B m⁻¹ hX)

theorem twistedOperator_le_lowerParabolicLie (m : B.Levi E) :
    (lowerParabolicLie B).restrictScalars F ≤
      ((lowerParabolicLie B).restrictScalars F).comap (twistedOperator B σ m) := by
  intro X hX
  change matrixSigma σ X - linearAdjoint (B.leviEmbedding E m⁻¹) X ∈ lowerParabolicLie B
  exact sub_mem (matrixSigma_mem_lowerParabolicLie B σ hX)
    (linearAdjoint_mem_lowerParabolicLie B m⁻¹ hX)

theorem twistedOperator_le_blockDiagonal (m : B.Levi E) :
    (blockDiagonalLieSubmodule B E).restrictScalars F ≤
      ((blockDiagonalLieSubmodule B E).restrictScalars F).comap (twistedOperator B σ m) := by
  intro X hX
  change matrixSigma σ X - linearAdjoint (B.leviEmbedding E m⁻¹) X ∈
    blockDiagonalLieSubmodule B E
  exact sub_mem (matrixSigma_mem_blockDiagonalLieSubmodule B σ hX)
    (linearAdjoint_mem_blockDiagonalLieSubmodule B m⁻¹ hX)

theorem twistedAdjointOperator_le_lowerLie (m : B.Levi E) :
    (lowerLie B).restrictScalars F ≤
      ((lowerLie B).restrictScalars F).comap (twistedAdjointOperator B σ m) := by
  intro X hX
  change matrixSigma σ.symm X - linearAdjoint (B.leviEmbedding E m) X ∈ lowerLie B
  exact sub_mem (matrixSigma_mem_lowerLie B σ.symm hX)
    (linearAdjoint_mem_lowerLie B m hX)

end Operators

section Pairing

/-- The trace pairing `⟨X, Y⟩ = Tr_{E/F}(tr(X Y))`. -/
def tracePairing : Matrix (Fin n) (Fin n) E →ₗ[F] Matrix (Fin n) (Fin n) E →ₗ[F] F :=
  (LinearMap.mul F (Matrix (Fin n) (Fin n) E)).compr₂
    ((Algebra.trace F E).comp ((Matrix.traceLinearMap (Fin n) E E).restrictScalars F))

theorem tracePairing_apply (X Y : Matrix (Fin n) (Fin n) E) :
    tracePairing (F := F) X Y = Algebra.trace F E (X * Y).trace := rfl

variable (σ : E ≃ₐ[F] E)

theorem tracePairing_adjoint (m : B.Levi E) (X Y : Matrix (Fin n) (Fin n) E) :
    tracePairing (F := F) (twistedOperator B σ m X) Y =
      tracePairing (F := F) X (twistedAdjointOperator B σ m Y) := by
  simp only [twistedOperator, twistedAdjointOperator, LinearMap.sub_apply, map_sub,
    LinearMap.sub_apply, LinearMap.restrictScalars_apply]
  congr 1
  · -- `⟨σ X, Y⟩ = ⟨X, σ⁻¹ Y⟩`.
    rw [tracePairing_apply, tracePairing_apply]
    have hprod : matrixSigma σ X * Y = (X * matrixSigma σ.symm Y).map σ := by
      rw [Matrix.map_mul]
      congr 1
      ext a b
      simp [matrixSigma_apply]
    have htr : ((X * matrixSigma σ.symm Y).map σ).trace =
        σ ((X * matrixSigma σ.symm Y).trace) := by
      simp [Matrix.trace, Matrix.diag, map_sum]
    rw [hprod, htr]
    exact Algebra.trace_eq_of_algEquiv σ _
  · -- `⟨m⁻¹ X m, Y⟩ = ⟨X, m Y m⁻¹⟩`.
    rw [tracePairing_apply, tracePairing_apply]
    congr 1
    change (((B.leviEmbedding E m⁻¹).val * (X * (B.leviEmbedding E m⁻¹)⁻¹.val)) * Y).trace =
      (X * ((B.leviEmbedding E m).val * (Y * (B.leviEmbedding E m)⁻¹.val))).trace
    rw [map_inv, inv_inv, ← map_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

theorem tracePairing_lowerParabolicLie_lowerLie {X Y : Matrix (Fin n) (Fin n) E}
    (hX : X ∈ lowerParabolicLie B) (hY : Y ∈ lowerLie B) : tracePairing (F := F) X Y = 0 := by
  rw [tracePairing_apply]
  have : (X * Y).trace = 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rcases lt_or_ge (B.coordinateBlock a) (B.coordinateBlock b) with h | h
    · rw [hX a b h, zero_mul]
    · rw [hY b a h, mul_zero]
  rw [this, map_zero]

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem eq_zero_of_forall_trace_mul {y : E} (h : ∀ c : E, Algebra.trace F E (c * y) = 0) :
    y = 0 := by
  have hnd := traceForm_nondegenerate F E
  apply hnd.2 y
  intro c
  exact h c

theorem tracePairing_separating {Y : Matrix (Fin n) (Fin n) E}
    (h : ∀ X, tracePairing (F := F) X Y = 0) : Y = 0 := by
  ext a b
  apply eq_zero_of_forall_trace_mul (F := F)
  intro c
  have := h (Matrix.single b a c)
  rw [tracePairing_apply, Matrix.trace_single_mul, smul_eq_mul] at this
  exact this

theorem mem_lowerParabolicLie_of_tracePairing {X : Matrix (Fin n) (Fin n) E}
    (h : ∀ Y ∈ lowerLie B, tracePairing (F := F) X Y = 0) : X ∈ lowerParabolicLie B := by
  intro a b hab
  apply eq_zero_of_forall_trace_mul (F := F)
  intro c
  have hY : Matrix.single b a c ∈ lowerLie B := by
    intro a' b' h'
    rw [Matrix.single_apply]
    split_ifs with h''
    · obtain ⟨rfl, rfl⟩ := h''
      exact absurd h' (not_le.mpr hab)
    · rfl
  have := h _ hY
  rw [tracePairing_apply, Matrix.trace_mul_single] at this
  simpa [mul_comm] using this

end Pairing

section Decomposition

variable [FiniteDimensional F E] [Algebra.IsSeparable F E] (σ : E ≃ₐ[F] E) (m : B.Levi E)

omit [Algebra.IsSeparable F E] in
/-- `D_{G/M,σ}(m)` is the determinant of `T` on `𝔤/𝔪`, computed with the `F`-quotient. -/
theorem twistedRelativeParabolicDiscriminant_eq_det_mapQ :
    twistedRelativeParabolicDiscriminant B σ m =
      LinearMap.det (((blockDiagonalLieSubmodule B E).restrictScalars F).mapQ
        ((blockDiagonalLieSubmodule B E).restrictScalars F) (twistedOperator B σ m)
        (twistedOperator_le_blockDiagonal B σ m)) := by
  let e := Submodule.Quotient.restrictScalarsEquiv F (blockDiagonalLieSubmodule B E)
  rw [twistedRelativeParabolicDiscriminant, ← LinearMap.det_conj _ e]
  congr 1
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro X
  have he : e.symm (Submodule.Quotient.mk X) = Submodule.Quotient.mk X := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
    Submodule.mapQ_apply]
  change relativeParabolicSigma B σ (Submodule.Quotient.mk X) -
      relativeParabolicAdjoint B E m⁻¹ (Submodule.Quotient.mk X) =
    Submodule.Quotient.mk (matrixSigma σ X - linearAdjoint (B.leviEmbedding E m⁻¹) X)
  rw [relativeParabolicSigma_mk, relativeParabolicAdjoint_mk, Submodule.Quotient.mk_sub]
  rfl

omit [Algebra.IsSeparable F E] in
/-- `D_{G/M,σ}(m) = det(T|𝔲̄) · det(T on 𝔤/𝔭̄)`. -/
theorem twistedRelativeParabolicDiscriminant_eq_mul_det_quotient :
    twistedRelativeParabolicDiscriminant B σ m =
      LinearMap.det ((twistedOperator B σ m).restrict (twistedOperator_le_lowerLie B σ m)) *
        LinearMap.det (((lowerParabolicLie (E := E) B).restrictScalars F).mapQ
          ((lowerParabolicLie (E := E) B).restrictScalars F) (twistedOperator B σ m)
          (twistedOperator_le_lowerParabolicLie B σ m)) := by
  rw [twistedRelativeParabolicDiscriminant_eq_det_mapQ]
  apply det_mapQ_eq_det_restrict_mul_det_mapQ
  · exact blockDiagonalLieSubmodule_le_lowerParabolicLie (E := E) B
  · rw [lowerParabolicLie_eq_sup, Submodule.restrictScalars_sup]
  · rw [Submodule.disjoint_def]
    intro x hx hy
    exact (Submodule.disjoint_def.mp (disjoint_blockDiagonalLieSubmodule_lowerLie B)) x hx hy

/-- `D_{G/M,σ}(m) = det(σ − Ad(m)⁻¹ | 𝔲̄) · det(σ⁻¹ − Ad(m) | 𝔲̄)`. -/
theorem twistedRelativeParabolicDiscriminant_eq_mul :
    twistedRelativeParabolicDiscriminant B σ m =
      LinearMap.det ((twistedOperator B σ m).restrict (twistedOperator_le_lowerLie B σ m)) *
        LinearMap.det ((twistedAdjointOperator B σ m).restrict
          (twistedAdjointOperator_le_lowerLie B σ m)) := by
  rw [twistedRelativeParabolicDiscriminant_eq_mul_det_quotient]
  congr 1
  apply det_mapQ_eq_det_restrict_of_pairing tracePairing
  · exact tracePairing_adjoint B σ m
  · intro x hx y hy
    exact tracePairing_lowerParabolicLie_lowerLie B hx hy
  · intro y _ hy
    exact tracePairing_separating hy
  · intro x hx
    exact mem_lowerParabolicLie_of_tracePairing B hx

end Decomposition

section Factorization

variable (σ : E ≃ₐ[F] E) (m : B.Levi E)

theorem matrixSigma_le_lowerLie :
    ∀ X ∈ (lowerLie (E := E) B).restrictScalars F,
      matrixSigma σ X ∈ (lowerLie (E := E) B).restrictScalars F :=
  fun _ hX => matrixSigma_mem_lowerLie B σ hX

theorem linearAdjoint_le_lowerLie (g : B.Levi E) :
    ∀ X ∈ (lowerLie (E := E) B).restrictScalars F,
      (linearAdjoint (B.leviEmbedding E g)).restrictScalars F X ∈
        (lowerLie (E := E) B).restrictScalars F :=
  fun _ hX => linearAdjoint_mem_lowerLie B g hX

theorem neg_linearAdjoint_le_lowerLie (g : B.Levi E) :
    ∀ X ∈ (lowerLie (E := E) B).restrictScalars F,
      (-(linearAdjoint (B.leviEmbedding E g)).restrictScalars F) X ∈
        (lowerLie (E := E) B).restrictScalars F :=
  fun _ hX => neg_mem (linearAdjoint_mem_lowerLie B g hX)

theorem linearAdjoint_leviEmbedding_inv_apply (g : B.Levi E) (X : Matrix (Fin n) (Fin n) E) :
    linearAdjoint (B.leviEmbedding E g) (linearAdjoint (B.leviEmbedding E g⁻¹) X) = X := by
  change (B.leviEmbedding E g).val * ((B.leviEmbedding E g⁻¹).val *
    (X * (B.leviEmbedding E g⁻¹)⁻¹.val) * (B.leviEmbedding E g)⁻¹.val) = X
  rw [map_inv, inv_inv]
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem matrixSigma_symm_apply_apply (X : Matrix (Fin n) (Fin n) E) :
    matrixSigma σ (matrixSigma σ.symm X) = X := by
  ext a b
  simp

/-- `σ⁻¹ − Ad(m) = −Ad(m) ∘ (σ − Ad(m)⁻¹) ∘ σ⁻¹` on `𝔲̄`. -/
theorem twistedAdjointOperator_restrict_eq :
    (twistedAdjointOperator B σ m).restrict (twistedAdjointOperator_le_lowerLie B σ m) =
      ((-(linearAdjoint (B.leviEmbedding E m)).restrictScalars F).restrict
          (neg_linearAdjoint_le_lowerLie B m)) ∘ₗ
        ((twistedOperator B σ m).restrict (twistedOperator_le_lowerLie B σ m)) ∘ₗ
        ((matrixSigma σ.symm).restrict (matrixSigma_le_lowerLie B σ.symm)) := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  change matrixSigma σ.symm X.val - linearAdjoint (B.leviEmbedding E m) X.val =
    -linearAdjoint (B.leviEmbedding E m) (matrixSigma σ (matrixSigma σ.symm X.val) -
      linearAdjoint (B.leviEmbedding E m⁻¹) (matrixSigma σ.symm X.val))
  rw [matrixSigma_symm_apply_apply, map_sub, linearAdjoint_leviEmbedding_inv_apply]
  abel

theorem det_twistedAdjointOperator_restrict :
    LinearMap.det ((twistedAdjointOperator B σ m).restrict
        (twistedAdjointOperator_le_lowerLie B σ m)) =
      LinearMap.det ((-(linearAdjoint (B.leviEmbedding E m)).restrictScalars F).restrict
          (neg_linearAdjoint_le_lowerLie B m)) *
        LinearMap.det ((twistedOperator B σ m).restrict (twistedOperator_le_lowerLie B σ m)) *
        LinearMap.det ((matrixSigma σ.symm).restrict (matrixSigma_le_lowerLie B σ.symm)) := by
  rw [twistedAdjointOperator_restrict_eq, LinearMap.det_comp, LinearMap.det_comp, mul_assoc]

theorem matrixSigma_iterate_apply (τ : E ≃ₐ[F] E) (k : ℕ) (X : Matrix (Fin n) (Fin n) E)
    (a b : Fin n) : ((matrixSigma τ)^[k] X) a b = (τ ^ k) (X a b) := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, matrixSigma_apply, pow_succ, AlgEquiv.mul_apply]

/-- `σ⁻¹` has finite order on `𝔲̄`, so its determinant has absolute value one. -/
theorem abv_det_matrixSigma_restrict [FiniteDimensional F E] (abv : AbsoluteValue F ℝ)
    (τ : E ≃ₐ[F] E) {l : ℕ} (hl : 0 < l) (hτ : τ ^ l = 1) :
    abv (LinearMap.det ((matrixSigma τ).restrict (matrixSigma_le_lowerLie B τ))) = 1 := by
  have hpow : ((matrixSigma τ).restrict (matrixSigma_le_lowerLie (E := E) B τ)) ^ l = 1 := by
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    rw [Module.End.pow_apply, Module.End.one_apply]
    have : ∀ k (Y : (lowerLie (E := E) B).restrictScalars F),
        (((matrixSigma τ).restrict (matrixSigma_le_lowerLie (E := E) B τ))^[k] Y).val =
          (matrixSigma τ)^[k] Y.val := by
      intro k
      induction k with
      | zero => intro Y; rfl
      | succ k ih =>
        intro Y
        rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
        rfl
    rw [this]
    ext a b
    rw [matrixSigma_iterate_apply, hτ, AlgEquiv.one_apply]
  have hdet := congrArg LinearMap.det hpow
  rw [map_pow, map_one] at hdet
  have habv := congrArg abv hdet
  rw [map_pow, map_one] at habv
  exact (pow_eq_one_iff_of_nonneg (abv.nonneg _) hl.ne').mp habv

end Factorization

section AbsoluteValue

variable [FiniteDimensional F E] [Algebra.IsSeparable F E] (σ : E ≃ₐ[F] E) (m : B.Levi E)

/-- `|D_{G/M,σ}(m)| = |det(σ − Ad(m)⁻¹ | 𝔲̄)|² · |det(Ad(m) | 𝔲̄)|` for `σ` of finite order. -/
theorem abv_twistedRelativeParabolicDiscriminant (abv : AbsoluteValue F ℝ) {l : ℕ} (hl : 0 < l)
    (hσ : σ ^ l = 1) :
    abv (twistedRelativeParabolicDiscriminant B σ m) =
      abv (LinearMap.det ((twistedOperator B σ m).restrict
          (twistedOperator_le_lowerLie B σ m))) ^ 2 *
        abv (LinearMap.det (((linearAdjoint (B.leviEmbedding E m)).restrictScalars F).restrict
          (linearAdjoint_le_lowerLie B m))) := by
  rw [twistedRelativeParabolicDiscriminant_eq_mul, det_twistedAdjointOperator_restrict]
  have hσ' : σ.symm ^ l = 1 := by
    rw [← AlgEquiv.aut_inv, inv_pow, hσ, inv_one]
  have hneg : ((-(linearAdjoint (B.leviEmbedding E m)).restrictScalars F).restrict
      (neg_linearAdjoint_le_lowerLie (F := F) B m)) =
      (-1 : F) • (((linearAdjoint (B.leviEmbedding E m)).restrictScalars F).restrict
        (linearAdjoint_le_lowerLie B m)) := by
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    simp
  have h1 : ∀ k : ℕ, abv ((-1 : F) ^ k) = 1 := fun k => by
    rw [map_pow, abv.map_neg, map_one, one_pow]
  rw [hneg, LinearMap.det_smul, map_mul, map_mul, map_mul, map_mul, h1, one_mul,
    abv_det_matrixSigma_restrict B abv σ.symm hl hσ']
  ring

end AbsoluteValue

end Langlands.BaseChange.TwistedLocalDescent
