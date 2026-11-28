import Langlands.Algebra.IdealTensorRelation
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Endomorphism reduction along a quotient of the coefficient ring -/

open scoped TensorProduct

namespace Langlands.Algebra

open IdealTensorRelation

variable {R M M₀ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (I : Ideal R) [AddCommGroup M₀] [Module (R ⧸ I) M₀] (E : (R ⧸ I) ⊗[R] M ≃ₗ[R ⧸ I] M₀)

local notation "T" => R ⧸ I

/-- The quotient map on elements in a given presentation of scalar extension. -/
abbrev quotientModuleMap (x : M) : M₀ := E ((1 : T) ⊗ₜ[R] x)

lemma quotientModuleMap_surjective : Function.Surjective (quotientModuleMap I E) := by
  intro y
  obtain ⟨x, hx⟩ := exists_eq_one_tmul I (E.symm y)
  exact ⟨x, by rw [quotientModuleMap, ← hx, LinearEquiv.apply_symm_apply]⟩

private def quotientEndRingHom : Module.End R M →+* Module.End T M₀ :=
  E.conjRingEquiv.toRingHom.comp (Module.End.baseChangeHom R T M).toRingHom

private lemma quotientEndRingHom_apply (f : Module.End R M) (x : M) :
    quotientEndRingHom I E f (quotientModuleMap I E x) = quotientModuleMap I E (f x) := by
  change E (f.baseChange T (E.symm (E ((1 : T) ⊗ₜ[R] x)))) = E ((1 : T) ⊗ₜ[R] f x)
  rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

variable [Algebra ℚ R] [Module ℚ M] [IsScalarTower ℚ R M]
  [Module ℚ M₀] [IsScalarTower ℚ (R ⧸ I) M₀]

/-- Reduce an endomorphism by scalar extension, then express it on the given
quotient module. -/
def quotientEndMap : Module.End R M →ₐ[ℚ] Module.End T M₀ where
  __ := quotientEndRingHom I E
  commutes' c := by
    ext y
    obtain ⟨x, rfl⟩ := quotientModuleMap_surjective I E y
    change quotientEndRingHom I E (algebraMap ℚ (Module.End R M) c) (quotientModuleMap I E x) = _
    rw [quotientEndRingHom_apply]
    change quotientModuleMap I E (c • x) = c • quotientModuleMap I E x
    calc
      _ = quotientModuleMap I E ((algebraMap ℚ R c) • x) := by rw [IsScalarTower.algebraMap_smul]
      _ = E ((algebraMap R T (algebraMap ℚ R c)) • ((1 : T) ⊗ₜ[R] x)) :=
        congrArg E (smul_one_tmul I (algebraMap ℚ R c) x).symm
      _ = _ := by rw [← IsScalarTower.algebraMap_apply ℚ R T, map_smul, IsScalarTower.algebraMap_smul]

@[simp]
lemma quotientEndMap_apply (f : Module.End R M) (x : M) :
    quotientEndMap I E f (quotientModuleMap I E x) = quotientModuleMap I E (f x) :=
  quotientEndRingHom_apply I E f x

/-- Endomorphisms of the quotient module lift when the original module is free. -/
theorem quotientEndMap_surjective [Module.Free R M] : Function.Surjective (quotientEndMap I E) := by
  classical
  let b := Module.Free.chooseBasis R M
  intro g
  choose x hx using fun i => quotientModuleMap_surjective I E (g (quotientModuleMap I E (b i)))
  refine ⟨b.constr R x, ((b.baseChange T).map E).ext fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
  change quotientEndMap I E (b.constr R x) (quotientModuleMap I E (b i)) = _
  rw [quotientEndMap_apply, Module.Basis.constr_basis, hx]

/-- For a square-zero ideal, the kernel of endomorphism reduction has square zero. -/
theorem quotientEndMap_sq_eq_zero (hI : I * I = ⊥) (f : Module.End R M)
    (hf : quotientEndMap I E f = 0) : f ^ 2 = 0 := by
  have hmem (x : M) : f x ∈ I • (⊤ : Submodule R M) := by
    have h := quotientEndMap_apply I E f x
    rw [hf, LinearMap.zero_apply] at h
    apply (one_tmul_eq_zero_iff I _).mp
    exact E.injective (h.symm.trans (map_zero E).symm)
  have hMap : (I • (⊤ : Submodule R M)).map f ≤ (⊥ : Submodule R M) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    calc
      I • LinearMap.range f ≤ I • (I • (⊤ : Submodule R M)) := by
        exact smul_le_smul_left _ (by rintro _ ⟨x, rfl⟩; exact hmem x)
      _ = ⊥ := by rw [← Submodule.mul_smul, hI, Submodule.bot_smul]
  ext x
  exact hMap (Submodule.mem_map_of_mem (hmem x))

end Langlands.Algebra
