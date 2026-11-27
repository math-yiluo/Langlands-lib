import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisGram

/-! # Local isometries from coboundary data

Let `c` be a crossed homomorphism of special unitary matrices for `H` over a finite Galois
extension `L/F`, with descended Gram matrix `H'`. Suppose that over a finite Galois extension
`M` of a field `K ⊇ F` receiving `L`, the extended values of `c` are the coboundary of a special
unitary matrix `b`. Then `H'` and `H` are isometric over `K`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  {K M : Type u} [Field K] [Field M] [Algebra F K] [Algebra F M] [Algebra K M]
  [IsScalarTower F K M]

theorem tensorIncl_injective : Function.Injective (tensorIncl (F := F) (D := D) (K := K) (M := M)) := by
  classical
  let b := Module.Free.chooseBasis F D
  let eM := TensorProduct.equivFinsuppOfBasisRight (M := M) b
  let eK := TensorProduct.equivFinsuppOfBasisRight (M := K) b
  have h : ∀ (z : K ⊗[F] D) i, eM (tensorIncl z) i = algebraMap K M (eK z i) := by
    intro z i
    induction z using TensorProduct.inductionOn with
    | tmul a d =>
      simp only [tensorIncl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, eM, eK,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, IsScalarTower.coe_toAlgHom']
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      simp [IsScalarTower.algebraMap_apply F K M]
    | add z z' hz hz' => simp only [map_add, Finsupp.add_apply, hz, hz']
  intro x y hxy
  apply eK.injective
  ext i
  apply (algebraMap K M).injective
  rw [← h, ← h, hxy]

theorem coeffMap_tower_injective {n : ℕ} :
    Function.Injective (coeffMap (n := n) (D := D) (IsScalarTower.toAlgHom F K M)) := by
  intro A B h
  ext i j
  exact tensorIncl_injective (congrFun (congrFun h i) j)

variable [FiniteDimensional K M] [IsGalois K M]

/-- A unit fixed by every automorphism of `M/K` descends to a unit over `K ⊗ D`. -/
theorem exists_unitMap_eq_of_fixed {n : ℕ} (T : (Matrix (Fin n) (Fin n) (M ⊗[F] D))ˣ)
    (hT : ∀ s : M ≃ₐ[K] M, unitMap (s.restrictScalars F).toAlgHom T = T) :
    ∃ t : (Matrix (Fin n) (Fin n) (K ⊗[F] D))ˣ, unitMap (IsScalarTower.toAlgHom F K M) t = T := by
  obtain ⟨B, hB⟩ := exists_coeffMap_eq_of_fixed (K := K) (M := M) (T : Matrix (Fin n) (Fin n)
    (M ⊗[F] D)) (fun s => congrArg Units.val (hT s))
  obtain ⟨B', hB'⟩ := exists_coeffMap_eq_of_fixed (K := K) (M := M) ((T⁻¹ : (Matrix (Fin n) (Fin n)
    (M ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (M ⊗[F] D)) (fun s => by
      rw [coeffMap_units_inv, hT s])
  have h1 : B * B' = 1 := by
    apply coeffMap_tower_injective (K := K) (M := M)
    rw [_root_.map_mul, hB, hB', Units.mul_inv, _root_.map_one]
  have h2 : B' * B = 1 := by
    apply coeffMap_tower_injective (K := K) (M := M)
    rw [_root_.map_mul, hB, hB', Units.inv_mul, _root_.map_one]
  exact ⟨⟨B, B', h1, h2⟩, Units.ext hB⟩

section Isometry

variable [Algebra.IsCentral F D] (τ : FirstKindInvolution F D) {n : ℕ} [NeZero n]
  (H : Matrix (Fin n) (Fin n) D)
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  [Algebra L M] [IsScalarTower F L M]

omit [FiniteDimensional F D] [FiniteDimensional K M] [IsGalois K M] [Algebra.IsCentral F D]
  [NeZero n] [FiniteDimensional F L] [IsGalois F L] in
/-- Restricting an automorphism of `M/K` to `L` is compatible with the coefficient maps. -/
theorem coeffMap_restrictNormal [Normal F L] (s : M ≃ₐ[K] M)
    (X : Matrix (Fin n) (Fin n) (L ⊗[F] D)) :
    coeffMap (s.restrictScalars F).toAlgHom (coeffMap (IsScalarTower.toAlgHom F L M) X) =
      coeffMap (IsScalarTower.toAlgHom F L M)
        (coeffMap ((s.restrictScalars F).restrictNormal L).toAlgHom X) := by
  have h : (s.restrictScalars F).toAlgHom.comp (IsScalarTower.toAlgHom F L M) =
      (IsScalarTower.toAlgHom F L M).comp ((s.restrictScalars F).restrictNormal L).toAlgHom := by
    ext x
    change (s.restrictScalars F) (algebraMap L M x) =
      algebraMap L M (((s.restrictScalars F).restrictNormal L) x)
    rw [AlgEquiv.restrictNormal_commutes]
  rw [coeffMap_comp, coeffMap_comp, h]

omit [FiniteDimensional F D] [FiniteDimensional K M] [IsGalois K M] [Algebra.IsCentral F D]
  [NeZero n] [FiniteDimensional F L] [IsGalois F L] in
theorem unitMap_restrictNormal [Normal F L] (s : M ≃ₐ[K] M)
    (X : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
    unitMap (s.restrictScalars F).toAlgHom (unitMap (IsScalarTower.toAlgHom F L M) X) =
      unitMap (IsScalarTower.toAlgHom F L M)
        (unitMap ((s.restrictScalars F).restrictNormal L).toAlgHom X) :=
  Units.ext (coeffMap_restrictNormal (K := K) (M := M) s _)

omit [FiniteDimensional F L] in
/-- Coboundary data over `M` give an isometry between the descended Gram matrix and `H`
over `K`. -/
theorem GramDescent.exists_isometry_of_coboundary
    {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ} (d : GramDescent τ H c)
    (b : (Matrix (Fin n) (Fin n) (M ⊗[F] D))ˣ) (hb : b ∈ suGroup τ H M)
    (hcob : ∀ s : M ≃ₐ[K] M, unitMap (IsScalarTower.toAlgHom F L M)
        (c ((s.restrictScalars F).restrictNormal L)) =
      b * (unitMap (s.restrictScalars F).toAlgHom b)⁻¹) :
    ∃ t : (Matrix (Fin n) (Fin n) (K ⊗[F] D))ˣ,
      (t : Matrix (Fin n) (Fin n) (K ⊗[F] D)) * gramOver n d.gram K *
        (τ.baseChange K).matrix (Fin n) t = gramOver n H K := by
  let ι := IsScalarTower.toAlgHom F L M
  let T := b⁻¹ * unitMap ι d.primitive
  have hT : ∀ s : M ≃ₐ[K] M, unitMap (s.restrictScalars F).toAlgHom T = T := by
    intro s
    set ρ := (s.restrictScalars F).restrictNormal L
    have h1 : (unitMap (s.restrictScalars F).toAlgHom b)⁻¹ = b⁻¹ * unitMap ι (c ρ) := by
      rw [hcob s, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : c ρ * unitMap ρ.toAlgHom d.primitive = d.primitive := by
      rw [d.coboundary ρ, mul_assoc, inv_mul_cancel, mul_one]
    change unitMap (s.restrictScalars F).toAlgHom (b⁻¹ * unitMap ι d.primitive) = _
    rw [_root_.map_mul, map_inv, h1, unitMap_restrictNormal (K := K) (M := M) s, mul_assoc,
      ← _root_.map_mul, h2]
  obtain ⟨t, ht⟩ := exists_unitMap_eq_of_fixed (K := K) (M := M) T hT
  refine ⟨t, ?_⟩
  apply coeffMap_tower_injective (K := K) (M := M)
  rw [_root_.map_mul, _root_.map_mul, coeffMap_adjoint, coeffMap_gramOver, coeffMap_gramOver]
  have hval : coeffMap (IsScalarTower.toAlgHom F K M) (t : Matrix (Fin n) (Fin n) (K ⊗[F] D)) =
      (T : Matrix (Fin n) (Fin n) (M ⊗[F] D)) := congrArg Units.val ht
  rw [hval]
  set adj := (τ.baseChange M).matrix (Fin n)
  set Bi : Matrix (Fin n) (Fin n) (M ⊗[F] D) := ((b⁻¹ : (Matrix (Fin n) (Fin n) (M ⊗[F] D))ˣ) :
    Matrix (Fin n) (Fin n) (M ⊗[F] D))
  set P : Matrix (Fin n) (Fin n) (M ⊗[F] D) := coeffMap ι (d.primitive : Matrix (Fin n) (Fin n)
    (L ⊗[F] D))
  have hP : P * gramOver n d.gram M * adj P = gramOver n H M := by
    have h := congrArg (coeffMap ι) d.gram_eq
    rw [_root_.map_mul, _root_.map_mul, coeffMap_adjoint, coeffMap_gramOver, coeffMap_gramOver] at h
    exact h
  have hBi : Bi * gramOver n H M * adj Bi = gramOver n H M := ((suGroup τ H M).inv_mem hb).1
  change Bi * P * gramOver n d.gram M * adj (Bi * P) = gramOver n H M
  rw [FirstKindInvolution.map_mul]
  calc Bi * P * gramOver n d.gram M * (adj P * adj Bi)
      = Bi * (P * gramOver n d.gram M * adj P) * adj Bi := by simp only [Matrix.mul_assoc]
    _ = gramOver n H M := by rw [hP, hBi]

end Isometry

end Langlands.GroupScheme.Quaternionic.SkewUnitary
