import Langlands.GroupScheme.Quaternionic.SkewUnitaryGalois
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois descent for coefficients in `M ⊗ D`

For a finite Galois extension `M/K` of fields over `F` and a finite-dimensional `F`-algebra
`D`, an element of `M ⊗[F] D` fixed by every automorphism of `M/K` comes from `K ⊗[F] D`;
the same holds entrywise for matrices.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
  {K M : Type u} [Field K] [Field M] [Algebra F K] [Algebra F M] [Algebra K M]
  [IsScalarTower F K M]

/-- The coefficient map `K ⊗ D → M ⊗ D`. -/
abbrev tensorIncl : K ⊗[F] D →ₐ[F] M ⊗[F] D :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom F K M) (AlgHom.id F D)

/-- The action of an automorphism of `M/K` on `M ⊗ D`. -/
abbrev tensorAut (s : M ≃ₐ[K] M) : M ⊗[F] D →ₐ[F] M ⊗[F] D :=
  Algebra.TensorProduct.map (s.restrictScalars F).toAlgHom (AlgHom.id F D)

variable [FiniteDimensional K M] [IsGalois K M]

/-- Fixed coefficients of `M ⊗ D` descend to `K ⊗ D`. -/
theorem exists_tensorIncl_eq_of_fixed (x : M ⊗[F] D) (hx : ∀ s : M ≃ₐ[K] M, tensorAut s x = x) :
    ∃ y : K ⊗[F] D, tensorIncl y = x := by
  classical
  let b := Module.Free.chooseBasis F D
  let eM := TensorProduct.equivFinsuppOfBasisRight (M := M) b
  let eK := TensorProduct.equivFinsuppOfBasisRight (M := K) b
  have haction (s : M ≃ₐ[K] M) (z : M ⊗[F] D) (i : Module.Free.ChooseBasisIndex F D) :
      eM (tensorAut s z) i = s (eM z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul a d =>
      simp only [tensorAut, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, eM,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply F K M,
        AlgEquiv.commutes]
      rfl
    | add z z' hz hz' => simp only [map_add, Finsupp.add_apply, hz, hz']
  have hcoeff (i : Module.Free.ChooseBasisIndex F D) : ∃ y : K, algebraMap K M y = eM x i := by
    apply IntermediateField.mem_bot.mp
    apply (IsGalois.mem_bot_iff_fixed _).mpr
    intro s
    rw [← haction, hx]
  choose y hy using hcoeff
  refine ⟨eK.symm (Finsupp.equivFunOnFinite.symm y), ?_⟩
  apply eM.injective
  ext i
  have h : ∀ z : K ⊗[F] D, eM (tensorIncl z) i = algebraMap K M (eK z i) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a d =>
      simp only [tensorIncl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, eM, eK,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, IsScalarTower.coe_toAlgHom']
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      simp [IsScalarTower.algebraMap_apply F K M]
    | add z z' hz hz' => simp only [map_add, Finsupp.add_apply, hz, hz']
  rw [h, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
  exact hy i

/-- A matrix over `M ⊗ D` fixed entrywise by every automorphism of `M/K` descends. -/
theorem exists_coeffMap_eq_of_fixed {n : ℕ} (A : Matrix (Fin n) (Fin n) (M ⊗[F] D))
    (hA : ∀ s : M ≃ₐ[K] M, coeffMap (s.restrictScalars F).toAlgHom A = A) :
    ∃ B : Matrix (Fin n) (Fin n) (K ⊗[F] D),
      coeffMap (IsScalarTower.toAlgHom F K M) B = A := by
  have h (i j : Fin n) : ∃ z : K ⊗[F] D, tensorIncl z = A i j := by
    apply exists_tensorIncl_eq_of_fixed
    intro s
    exact congrFun (congrFun (hA s) i) j
  choose B hB using h
  exact ⟨Matrix.of B, by ext i j; exact hB i j⟩

end Langlands.GroupScheme.Quaternionic.SkewUnitary
