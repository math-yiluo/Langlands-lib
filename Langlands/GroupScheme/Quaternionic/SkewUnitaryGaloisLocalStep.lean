import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisStabilizer

/-! # Local transfer of coboundary data to the block cocycle

If the original crossed homomorphism has coboundary data over every finite Galois extension of
a field `K ⊇ F`, and proper Witt transitivity holds over `K`, then the block crossed
homomorphism obtained by twisting into the stabilizer of the last row also has coboundary data
over every such extension.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D] (τ : FirstKindInvolution F D)

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem tensorIncl_matrixSesqBilin {n : ℕ} {K M : Type u} [Field K] [Field M] [Algebra F K]
    [Algebra F M] [Algebra K M] [IsScalarTower F K M] (G : Matrix (Fin n) (Fin n) (K ⊗[F] D))
    (x y : Fin n → K ⊗[F] D) :
    tensorIncl ((τ.baseChange K).matrixSesqBilin G x y) =
      (τ.baseChange M).matrixSesqBilin (coeffMap (IsScalarTower.toAlgHom F K M) G)
        (fun j => tensorIncl (x j)) (fun j => tensorIncl (y j)) := by
  simp only [FirstKindInvolution.matrixSesqBilin, LinearMap.mk₂_apply, map_sum, map_mul,
    coeffMap_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [τ.map_baseChange]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem unitMap_fixes_base {n : ℕ} {K M : Type u} [Field K] [Field M] [Algebra F K]
    [Algebra F M] [Algebra K M] [IsScalarTower F K M] (s : M ≃ₐ[K] M)
    (p : (Matrix (Fin n) (Fin n) (K ⊗[F] D))ˣ) :
    unitMap (s.restrictScalars F).toAlgHom (unitMap (IsScalarTower.toAlgHom F K M) p) =
      unitMap (IsScalarTower.toAlgHom F K M) p := by
  apply Units.ext
  change coeffMap (s.restrictScalars F).toAlgHom (coeffMap (IsScalarTower.toAlgHom F K M)
    (p : Matrix (Fin n) (Fin n) (K ⊗[F] D))) = coeffMap (IsScalarTower.toAlgHom F K M) p
  rw [coeffMap_comp]
  congr 2
  ext x
  change s (algebraMap K M x) = algebraMap K M x
  exact s.commutes x

variable {m : ℕ} [NeZero m] (H₁ : Matrix (Fin m) (Fin m) D) (c0 : D)
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [FiniteDimensional F L] in
/-- Local transfer of coboundary data from a crossed homomorphism to its block twist. -/
theorem IsCoboundaryAt.block (hc0 : IsUnit c0)
    (hanti : τ.matrix (Fin (m + 1)) (adjoinSkewLine H₁ c0) = -adjoinSkewLine H₁ c0)
    (hunit : IsUnit (adjoinSkewLine H₁ c0))
    {c : (L ≃ₐ[F] L) → (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ}
    (u : (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ)
    (hu : u ∈ suGroup τ (adjoinSkewLine H₁ c0) L)
    (c₁ : (L ≃ₐ[F] L) → (Matrix (Fin m) (Fin m) (L ⊗[F] D))ˣ)
    (hc₁ : ∀ s, blockUnit L (c₁ s) = u * c s * (unitMap s.toAlgHom u)⁻¹)
    (K : Type u) [Field K] [Algebra F K] (hW : ProperWittAt τ K (m + 1))
    (hK : IsCoboundaryAt τ (adjoinSkewLine H₁ c0) c K) : IsCoboundaryAt τ H₁ c₁ K := by
  intro M _ _ _ _ _ _ _ _
  obtain ⟨b, hb, hcob⟩ := hK M
  set H := adjoinSkewLine H₁ c0
  set b' := unitMap (IsScalarTower.toAlgHom F L M) u * b
  have hb' : b' ∈ suGroup τ H M := (suGroup τ H M).mul_mem (unitMap_mem τ (IsScalarTower.toAlgHom F L M) hu) hb
  have hcob' : ∀ s : M ≃ₐ[K] M,
      unitMap (IsScalarTower.toAlgHom F L M) (blockUnit L (c₁ ((s.restrictScalars F).restrictNormal L))) =
        b' * (unitMap (s.restrictScalars F).toAlgHom b')⁻¹ := by
    intro s
    rw [hc₁, _root_.map_mul, _root_.map_mul, map_inv, hcob s, ← unitMap_restrictNormal (K := K) s]
    simp only [b', _root_.map_mul]
    group
  -- the last row of `b'` is fixed by the relative Galois group
  set y : Fin (m + 1) → M ⊗[F] D := lastRow M ᵥ* (b' : Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D))
  have hyfix : ∀ (s : M ≃ₐ[K] M) (j : Fin (m + 1)), tensorAut s (y j) = y j := by
    intro s j
    have hs : unitMap (s.restrictScalars F).toAlgHom b' =
        (unitMap (IsScalarTower.toAlgHom F L M) (blockUnit L (c₁ ((s.restrictScalars F).restrictNormal L))))⁻¹ * b' := by
      rw [hcob' s]
      group
    have h1 : tensorAut s (y j) = (lastRow M ᵥ* coeffMap (s.restrictScalars F).toAlgHom
        (b' : Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D))) j := by
      have := RingHom.map_vecMul (tensorAut (F := F) (D := D) s).toRingHom
        (b' : Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D)) (lastRow M) j
      convert this using 2
      all_goals first
        | rfl
        | (funext k
           by_cases hk : k = Fin.last m
           · subst hk
             simp [lastRow]
           · simp [lastRow, Pi.single_eq_of_ne hk])
    rw [h1, ← val_unitMap, hs, Units.val_mul, ← Matrix.vecMul_vecMul, unitMap_blockUnit,
      ← map_inv, lastRow_vecMul_blockUnit]
  have hy : ∀ j, ∃ z : K ⊗[F] D, tensorIncl z = y j := fun j =>
    exists_tensorIncl_eq_of_fixed (K := K) (M := M) (y j) (fun s => hyfix s j)
  choose yK hyK using hy
  have hlast : (gramOver (m + 1) H M) (Fin.last m) (Fin.last m) =
      (Algebra.TensorProduct.includeRight c0 : M ⊗[F] D) := by
    simp [gramOver, H, adjoinSkewLine_last]
  have hlastK : (gramOver (m + 1) H K) (Fin.last m) (Fin.last m) =
      (Algebra.TensorProduct.includeRight c0 : K ⊗[F] D) := by
    simp [gramOver, H, adjoinSkewLine_last]
  -- the value of the descended row
  have hyval : (τ.baseChange M).matrixSesqBilin (gramOver (m + 1) H M) y y =
      Algebra.TensorProduct.includeRight c0 := by
    have hrow : y = (b' : Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D)) (Fin.last m) :=
      lastRow_vecMul M _
    rw [hrow, matrixSesqBilin_row, hb'.1, hlast]
  have hyKval : (τ.baseChange K).matrixSesqBilin (gramOver (m + 1) H K) yK yK =
      Algebra.TensorProduct.includeRight c0 := by
    apply tensorIncl_injective (K := K) (M := M)
    rw [tensorIncl_matrixSesqBilin, coeffMap_gramOver]
    have : (fun j => tensorIncl (yK j)) = y := funext hyK
    rw [this, hyval]
    simp [tensorIncl]
  have hone : lastRow K = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (K ⊗[F] D)) (Fin.last m) := by
    funext j
    simp only [lastRow, Matrix.one_apply, Pi.single_apply, eq_comm]
  have hlastval : (τ.baseChange K).matrixSesqBilin (gramOver (m + 1) H K) (lastRow K) (lastRow K) =
      Algebra.TensorProduct.includeRight c0 := by
    rw [hone, matrixSesqBilin_row, Matrix.one_mul, FirstKindInvolution.map_one, Matrix.mul_one,
      hlastK]
  have hGanti : (τ.baseChange K).matrix (Fin (m + 1)) (gramOver (m + 1) H K) =
      -gramOver (m + 1) H K := by
    rw [adjoint_gramOver, hanti]
    ext i j
    simp [gramOver, TensorProduct.tmul_neg]
  obtain ⟨p, hpH, hpN, hpx⟩ := hW (gramOver (m + 1) H K) hGanti (gramOver_isUnit K hunit)
    (lastRow K) yK (by rw [hlastval]; exact hc0.map Algebra.TensorProduct.includeRight)
    (hlastval.trans hyKval.symm)
  have hpSU : p ∈ suGroup τ H K := ⟨hpH, hpN⟩
  set X := unitMap (IsScalarTower.toAlgHom F K M) p
  set b'' := b' * X⁻¹
  have hb'' : b'' ∈ suGroup τ H M :=
    (suGroup τ H M).mul_mem hb' ((suGroup τ H M).inv_mem (unitMap_mem τ _ hpSU))
  have hyX : y = lastRow M ᵥ* (X : Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D)) := by
    funext j
    rw [← hyK j, ← hpx, tensorIncl_vecMul]
    congr 1
    funext k
    exact tensorIncl_lastRow k
  have hfix'' : lastRow M ᵥ* (b'' : Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D)) = lastRow M := by
    change lastRow M ᵥ* ((b' : Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D)) *
      ((X⁻¹ : (Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D))ˣ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (M ⊗[F] D))) = lastRow M
    rw [← Matrix.vecMul_vecMul]
    change y ᵥ* _ = _
    rw [hyX, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  have hcob'' : ∀ s : M ≃ₐ[K] M,
      unitMap (IsScalarTower.toAlgHom F L M) (blockUnit L (c₁ ((s.restrictScalars F).restrictNormal L))) =
        b'' * (unitMap (s.restrictScalars F).toAlgHom b'')⁻¹ := by
    intro s
    rw [hcob' s]
    simp only [b'', _root_.map_mul, map_inv, X, unitMap_fixes_base]
    group
  obtain ⟨b₁, hb₁⟩ := exists_blockUnit_of_fix τ H₁ c0 hc0 M b'' hb'' hfix''
  refine ⟨b₁, (blockUnit_mem_iff τ H₁ c0 M b₁).mp (hb₁ ▸ hb''), fun s => ?_⟩
  apply blockUnit_injective M
  rw [← unitMap_blockUnit, hcob'' s, ← hb₁, _root_.map_mul, map_inv, unitMap_blockUnit]

end Langlands.GroupScheme.Quaternionic.SkewUnitary
