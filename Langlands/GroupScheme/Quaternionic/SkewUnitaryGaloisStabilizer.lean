import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisRepresentation
import Langlands.GroupScheme.Quaternionic.SkewLineStabilizer

/-! # Block special unitary matrices for an adjoined line

For `H = adjoinSkewLine H₁ c` with `c` a unit, the special unitary matrices fixing the last
standard row are exactly the block matrices `adjoinSkewLine v 1` with `v` special unitary for
`H₁`.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]

section Block

variable {m : ℕ}

omit [DivisionRing D] in
theorem coeffMap_adjoinSkewLine {D : Type u} [Ring D] [Algebra F D] {R S : Type u} [CommRing R]
    [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (P : Matrix (Fin m) (Fin m) (R ⊗[F] D)) (a : R ⊗[F] D) :
    (adjoinSkewLine P a).map (Algebra.TensorProduct.map f (AlgHom.id F D)) =
      adjoinSkewLine (P.map (Algebra.TensorProduct.map f (AlgHom.id F D)))
        (Algebra.TensorProduct.map f (AlgHom.id F D) a) :=
  map_adjoinSkewLine (Algebra.TensorProduct.map f (AlgHom.id F D)).toRingHom P a

omit [DivisionRing D] [Algebra F D] in
theorem adjoinSkewLine_one_one {A : Type u} [Ring A] :
    adjoinSkewLine (1 : Matrix (Fin m) (Fin m) A) 1 = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [adjoinSkewLine_last]
  · simp [adjoinSkewLine_last_castSucc, (Fin.castSucc_ne_last j).symm]
  · simp [adjoinSkewLine_castSucc_last, Fin.castSucc_ne_last i]
  · simp [adjoinSkewLine_castSucc, Matrix.one_apply]

/-- The block unit `adjoinSkewLine v 1`. -/
def blockUnit (R : Type u) [CommRing R] [Algebra F R] :
    (Matrix (Fin m) (Fin m) (R ⊗[F] D))ˣ →* (Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D))ˣ where
  toFun v := ⟨adjoinSkewLine (v : Matrix (Fin m) (Fin m) (R ⊗[F] D)) 1,
    adjoinSkewLine ((v⁻¹ : (Matrix (Fin m) (Fin m) (R ⊗[F] D))ˣ) :
      Matrix (Fin m) (Fin m) (R ⊗[F] D)) 1,
    by rw [adjoinSkewLine_mul, Units.mul_inv, mul_one, adjoinSkewLine_one_one],
    by rw [adjoinSkewLine_mul, Units.inv_mul, mul_one, adjoinSkewLine_one_one]⟩
  map_one' := by
    apply Units.ext
    change adjoinSkewLine (1 : Matrix (Fin m) (Fin m) (R ⊗[F] D)) 1 = 1
    exact adjoinSkewLine_one_one
  map_mul' v w := by
    apply Units.ext
    change adjoinSkewLine _ 1 = adjoinSkewLine _ 1 * adjoinSkewLine _ 1
    rw [adjoinSkewLine_mul, mul_one]
    rfl

@[simp] theorem val_blockUnit (R : Type u) [CommRing R] [Algebra F R]
    (v : (Matrix (Fin m) (Fin m) (R ⊗[F] D))ˣ) :
    (blockUnit R v : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D)) =
      adjoinSkewLine (v : Matrix (Fin m) (Fin m) (R ⊗[F] D)) 1 :=
  rfl

theorem blockUnit_injective (R : Type u) [CommRing R] [Algebra F R] :
    Function.Injective (blockUnit (F := F) (D := D) (m := m) R) := by
  intro v w h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [val_blockUnit] at h'
  ext i j
  have := congrFun (congrFun h' i.castSucc) j.castSucc
  simpa only [adjoinSkewLine_castSucc] using this

theorem unitMap_blockUnit {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (v : (Matrix (Fin m) (Fin m) (R ⊗[F] D))ˣ) :
    unitMap f (blockUnit R v) = blockUnit S (unitMap f v) := by
  apply Units.ext
  rw [val_unitMap, val_blockUnit, val_blockUnit, val_unitMap, coeffMap_apply,
    coeffMap_adjoinSkewLine, _root_.map_one]
  rfl

/-- The last standard row. -/
def lastRow (R : Type u) [CommRing R] [Algebra F R] : Fin (m + 1) → R ⊗[F] D :=
  Pi.single (Fin.last m) 1

end Block

section SU

variable [Algebra.IsCentral F D] [FiniteDimensional F D] (τ : FirstKindInvolution F D)
  {m : ℕ} [NeZero m] (H₁ : Matrix (Fin m) (Fin m) D) (c0 : D)

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero m] in
theorem gramOver_adjoinSkewLine (R : Type u) [CommRing R] [Algebra F R] :
    gramOver (m + 1) (adjoinSkewLine H₁ c0) R =
      adjoinSkewLine (gramOver m H₁ R) (Algebra.TensorProduct.includeRight c0 : R ⊗[F] D) :=
  map_adjoinSkewLine (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D).toRingHom H₁ c0

theorem blockUnit_mem_iff (R : Type u) [CommRing R] [Algebra F R]
    (v : (Matrix (Fin m) (Fin m) (R ⊗[F] D))ˣ) :
    blockUnit R v ∈ suGroup τ (adjoinSkewLine H₁ c0) R ↔ v ∈ suGroup τ H₁ R := by
  rw [mem_suGroup, mem_suGroup]
  simp only [IsSU, val_blockUnit, gramOver_adjoinSkewLine, FirstKindInvolution.matrix_adjoinSkewLine,
    FirstKindInvolution.map_one, adjoinSkewLine_mul, one_mul, mul_one,
    matrixReducedNorm_adjoinSkewLine_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    ext i j
    have := congrFun (congrFun h1 i.castSucc) j.castSucc
    simpa only [adjoinSkewLine_castSucc] using this
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1], h2⟩

/-- A special unitary matrix for the adjoined form fixing the last row is a block unit. -/
theorem exists_blockUnit_of_fix (hc0 : IsUnit c0) (R : Type u) [CommRing R] [Algebra F R]
    (w : (Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D))ˣ)
    (hw : w ∈ suGroup τ (adjoinSkewLine H₁ c0) R)
    (hfix : lastRow R ᵥ* (w : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D)) = lastRow R) :
    ∃ v : (Matrix (Fin m) (Fin m) (R ⊗[F] D))ˣ, blockUnit R v = w := by
  have hc : IsUnit (Algebra.TensorProduct.includeRight c0 : R ⊗[F] D) :=
    hc0.map (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D)
  have hw' := hw
  rw [mem_suGroup, IsSU, gramOver_adjoinSkewLine] at hw'
  obtain ⟨P, hP, -, -, hM⟩ := (skewLineStabilizer F D R τ m (gramOver m H₁ R)
    (Algebra.TensorProduct.includeRight c0) hc (w : Matrix (Fin (m + 1)) (Fin (m + 1))
      (R ⊗[F] D)) w.isUnit).mp ⟨hw'.1, hw'.2, hfix⟩
  refine ⟨hP.unit, Units.ext ?_⟩
  rw [val_blockUnit, IsUnit.unit_spec, hM]

end SU

section Twist

variable {n : ℕ} {L : Type u} [Field L] [Algebra F L]

theorem unitMap_mul_aut (s t : L ≃ₐ[F] L) (X : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
    unitMap (s * t).toAlgHom X = unitMap s.toAlgHom (unitMap t.toAlgHom X) := by
  apply Units.ext
  rw [val_unitMap, val_unitMap, val_unitMap, coeffMap_comp]
  rfl

/-- Twisting a crossed homomorphism by a unit. -/
theorem IsCrossed.twist {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ}
    (hc : IsCrossed c) (u : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
    IsCrossed (fun s => u * c s * (unitMap s.toAlgHom u)⁻¹) := by
  intro s t
  simp only [hc s t, unitMap_mul_aut, _root_.map_mul, map_inv]
  group

end Twist

section Step

variable [Algebra.IsCentral F D] [FiniteDimensional F D] (τ : FirstKindInvolution F D)
  {m : ℕ} [NeZero m] (H₁ : Matrix (Fin m) (Fin m) D) (c0 : D)
  {L : Type u} [Field L] [Algebra F L]

/-- The twisted crossed homomorphism fixing the last row is a block crossed homomorphism. -/
theorem exists_block_cocycle (hc0 : IsUnit c0)
    {c : (L ≃ₐ[F] L) → (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ} (hc : IsCrossed c)
    (hsu : ∀ s, c s ∈ suGroup τ (adjoinSkewLine H₁ c0) L)
    (u : (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ)
    (hu : u ∈ suGroup τ (adjoinSkewLine H₁ c0) L)
    (hfix : ∀ s, lastRow L ᵥ* ((u * c s * (unitMap s.toAlgHom u)⁻¹ :
      (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D)) = lastRow L) :
    ∃ c₁ : (L ≃ₐ[F] L) → (Matrix (Fin m) (Fin m) (L ⊗[F] D))ˣ,
      IsCrossed c₁ ∧ (∀ s, c₁ s ∈ suGroup τ H₁ L) ∧
        ∀ s, blockUnit L (c₁ s) = u * c s * (unitMap s.toAlgHom u)⁻¹ := by
  have hmem : ∀ s, u * c s * (unitMap s.toAlgHom u)⁻¹ ∈ suGroup τ (adjoinSkewLine H₁ c0) L :=
    fun s => (suGroup τ _ L).mul_mem ((suGroup τ _ L).mul_mem hu (hsu s))
      ((suGroup τ _ L).inv_mem (unitMap_mem τ _ hu))
  choose c₁ hc₁ using fun s => exists_blockUnit_of_fix τ H₁ c0 hc0 L _ (hmem s) (hfix s)
  refine ⟨c₁, ?_, fun s => ?_, hc₁⟩
  · intro s t
    apply blockUnit_injective L
    rw [hc₁, _root_.map_mul, hc₁, ← unitMap_blockUnit, hc₁]
    exact hc.twist u s t
  · rw [← blockUnit_mem_iff τ H₁ c0, hc₁]
    exact hmem s

/-- A coboundary of the block crossed homomorphism gives a coboundary of the original one. -/
theorem exists_coboundary_of_block
    {c : (L ≃ₐ[F] L) → (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ}
    (u : (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ)
    (hu : u ∈ suGroup τ (adjoinSkewLine H₁ c0) L)
    (c₁ : (L ≃ₐ[F] L) → (Matrix (Fin m) (Fin m) (L ⊗[F] D))ˣ)
    (hc₁ : ∀ s, blockUnit L (c₁ s) = u * c s * (unitMap s.toAlgHom u)⁻¹)
    (a₁ : (Matrix (Fin m) (Fin m) (L ⊗[F] D))ˣ) (ha₁ : a₁ ∈ suGroup τ H₁ L)
    (hcob : ∀ s, c₁ s = a₁ * (unitMap s.toAlgHom a₁)⁻¹) :
    ∃ a ∈ suGroup τ (adjoinSkewLine H₁ c0) L, ∀ s, c s = a * (unitMap s.toAlgHom a)⁻¹ := by
  refine ⟨u⁻¹ * blockUnit L a₁, (suGroup τ _ L).mul_mem ((suGroup τ _ L).inv_mem hu)
    ((blockUnit_mem_iff τ H₁ c0 L a₁).mpr ha₁), fun s => ?_⟩
  have h := hc₁ s
  rw [hcob s, _root_.map_mul, map_inv, ← unitMap_blockUnit] at h
  rw [_root_.map_mul, map_inv]
  have hcs : c s = u⁻¹ * (u * c s * (unitMap s.toAlgHom u)⁻¹) * unitMap s.toAlgHom u := by group
  rw [hcs, ← h]
  group

end Step

section RowLemmas

variable {m : ℕ}

theorem lastRow_vecMul (R : Type u) [CommRing R] [Algebra F R]
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D)) :
    lastRow R ᵥ* B = B (Fin.last m) := by
  rw [lastRow, Matrix.single_one_vecMul]
  rfl

theorem lastRow_vecMul_blockUnit (R : Type u) [CommRing R] [Algebra F R]
    (v : (Matrix (Fin m) (Fin m) (R ⊗[F] D))ˣ) :
    lastRow R ᵥ* (blockUnit R v : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D)) = lastRow R := by
  rw [lastRow_vecMul, val_blockUnit]
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [adjoinSkewLine_last, lastRow]
  · simp [adjoinSkewLine_last_castSucc, lastRow]

theorem tensorIncl_vecMul {K M : Type u} [Field K] [Field M] [Algebra F K] [Algebra F M]
    [Algebra K M] [IsScalarTower F K M] (x : Fin (m + 1) → K ⊗[F] D)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (K ⊗[F] D)) (i : Fin (m + 1)) :
    tensorIncl ((x ᵥ* B) i) =
      ((fun j => tensorIncl (x j)) ᵥ* coeffMap (IsScalarTower.toAlgHom F K M) B) i :=
  RingHom.map_vecMul (tensorIncl (F := F) (D := D) (K := K) (M := M)).toRingHom B x i

theorem tensorIncl_lastRow {K M : Type u} [Field K] [Field M] [Algebra F K] [Algebra F M]
    [Algebra K M] [IsScalarTower F K M] (j : Fin (m + 1)) :
    tensorIncl (F := F) (D := D) (K := K) (M := M) (lastRow K j) = lastRow M j := by
  by_cases h : j = Fin.last m
  · subst h
    simp [lastRow]
  · simp [lastRow, Pi.single_eq_of_ne h]

end RowLemmas

section Local

variable [Algebra.IsCentral F D] [FiniteDimensional F D] (τ : FirstKindInvolution F D)

/-- Proper Witt transitivity for antihermitian Gram matrices of size `N` over `K ⊗ D`. -/
def ProperWittAt (K : Type u) [Field K] [Algebra F K] (N : ℕ) [NeZero N] : Prop :=
  ∀ (G : Matrix (Fin N) (Fin N) (K ⊗[F] D)), (τ.baseChange K).matrix (Fin N) G = -G → IsUnit G →
    ∀ x y : Fin N → K ⊗[F] D, IsUnit ((τ.baseChange K).matrixSesqBilin G x x) →
      (τ.baseChange K).matrixSesqBilin G x x = (τ.baseChange K).matrixSesqBilin G y y →
      ∃ p : (Matrix (Fin N) (Fin N) (K ⊗[F] D))ˣ,
        (p : Matrix (Fin N) (Fin N) (K ⊗[F] D)) * G *
            (τ.baseChange K).matrix (Fin N) (p : Matrix (Fin N) (Fin N) (K ⊗[F] D)) = G ∧
          matrixReducedNorm K (p : Matrix (Fin N) (Fin N) (K ⊗[F] D)) = 1 ∧
            x ᵥ* (p : Matrix (Fin N) (Fin N) (K ⊗[F] D)) = y

end Local

end Langlands.GroupScheme.Quaternionic.SkewUnitary
