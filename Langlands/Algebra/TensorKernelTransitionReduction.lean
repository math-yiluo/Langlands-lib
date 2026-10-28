import Langlands.Algebra.TensorKernelTransitionReductionStatement
import Langlands.Algebra.IdealTensorBaseChangeRelation
import Mathlib.RingTheory.Localization.BaseChange

/-! # Proof of the tensor-kernel transition reduction for Stacks 00MO -/

open scoped TensorProduct

namespace Langlands.Algebra
namespace TensorKernelTransitionReduction

open IdealTensorRelation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R R' S S' M M' : Type*}
  [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra R S] [Algebra S S'] [Algebra R' S'] [Algebra R S']
  [IsScalarTower R S S'] [IsScalarTower R R' S']
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup M'] [Module R' M'] [Module S M'] [Module S' M']
  [IsScalarTower R' S' M'] [IsScalarTower S S' M']

variable (R R' S S') in
/-- The algebra structure of `S'` over `S ⊗[R] R'` given by the product map. -/
abbrev productAlgebra : Algebra (S ⊗[R] R') S' :=
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R S S')
    (IsScalarTower.toAlgHom R R' S')).toRingHom.toAlgebra

theorem productAlgebra_algebraMap_tmul (s : S) (a : R') :
    letI := productAlgebra R R' S S'
    algebraMap (S ⊗[R] R') S' (s ⊗ₜ a) = algebraMap S S' s * algebraMap R' S' a := by
  simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.productMap_apply_tmul]

/-- The reduction, with the localization hypothesis stated through `productAlgebra`. -/
theorem reduction (I : Ideal R) (W : Submonoid (S ⊗[R] R')) (f : M →ₗ[S] M') (hI : I.FG)
    (hloc : letI := productAlgebra R R' S S'; IsLocalization W S')
    (hbc : IsBaseChange S' f) (hflat : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M))
    (htor : ∀ (n : ℕ) (a : Fin n → I) (m : Fin n → M), ∑ k, (a k : R) • m k = 0 →
      ∑ k, (⟨algebraMap R R' (a k), Ideal.mem_map_of_mem _ (a k).2⟩ :
          I.map (algebraMap R R')) ⊗ₜ[R'] f (m k) = 0) :
    Function.Injective (LinearMap.rTensor M' (I.map (algebraMap R R')).subtype) ∧
      Module.Flat (R' ⧸ I.map (algebraMap R R'))
        ((R' ⧸ I.map (algebraMap R R')) ⊗[R'] M') := by
  let := productAlgebra R R' S S'
  have : IsLocalization W S' := hloc
  -- The scalar towers through `T = S ⊗[R] R'`.
  have hST : IsScalarTower S (S ⊗[R] R') S' := IsScalarTower.of_algebraMap_eq fun s ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      productAlgebra_algebraMap_tmul, map_one, mul_one]
  have hR'T : IsScalarTower R' (S ⊗[R] R') S' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [Algebra.TensorProduct.right_algebraMap_apply, productAlgebra_algebraMap_tmul, map_one,
      one_mul]
  let : Module (S ⊗[R] R') M' := Module.compHom M' (algebraMap (S ⊗[R] R') S')
  have hTS' : IsScalarTower (S ⊗[R] R') S' M' :=
    ⟨fun t s m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : IsScalarTower S (S ⊗[R] R') M' := IsScalarTower.to₁₂₄ S (S ⊗[R] R') S' M'
  have : IsScalarTower R' (S ⊗[R] R') M' := IsScalarTower.to₁₂₄ R' (S ⊗[R] R') S' M'
  -- The localization `ψ : T ⊗[S] M → M'`.
  let ψ : (S ⊗[R] R') ⊗[S] M →ₗ[S ⊗[R] R'] M' := LinearMap.liftBaseChange (S ⊗[R] R') f
  have hψ : ∀ m, ψ (1 ⊗ₜ m) = f m := fun m ↦ by simp [ψ]
  have hc : IsBaseChange S'
      ((ψ : (S ⊗[R] R') ⊗[S] M →ₗ[S] M') ∘ₗ TensorProduct.mk S (S ⊗[R] R') M 1) := by
    convert hbc using 1
    ext m
    exact hψ m
  have hψbc : IsBaseChange S' ψ := IsBaseChange.of_comp (TensorProduct.isBaseChange S M _) hc
  have : IsLocalizedModule W ψ := (isLocalizedModule_iff_isBaseChange W S' ψ).mpr hψbc
  -- The comparison `T ⊗[S] M ≃ R' ⊗[R] M`.
  let e : (S ⊗[R] R') ⊗[S] M ≃ₗ[R'] R' ⊗[R] M :=
    Algebra.IsPushout.cancelBaseChange R R' S (S ⊗[R] R') M
  have he : ∀ m : M, ψ (e.symm ((1 : R') ⊗ₜ[R] m)) = f m := fun m ↦ by
    rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, hψ]
  -- Generators of `I`.
  obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  let g : Fin r → I := fun k ↦ ⟨s k, hs ▸ Submodule.subset_span ⟨k, rfl⟩⟩
  have hg : Ideal.span (Set.range fun k ↦ (g k : R)) = I := hs
  have hg' := span_mapGen (R' := R') I g hg
  -- Relations in `T ⊗[S] M` have vanishing generator tensor in `M'`.
  have hrelP : ∀ p : Fin r → (S ⊗[R] R') ⊗[S] M,
      ∑ k, (mapGen (R' := R') I g k : R') • p k = 0 →
      ∑ k, mapGen (R' := R') I g k ⊗ₜ[R'] ψ (p k) = 0 := by
    intro p hp
    have hy : ∑ k, algebraMap R R' (g k) • e (p k) = 0 := by
      rw [← map_zero e, ← hp, map_sum]
      simp only [map_smul]
    have hmem := sum_tmul_mem_relationSpan I g M hg (fun k ↦ e (p k)) hy
    let Φ : R' ⊗[R] M →ₗ[R'] M' := ψ.restrictScalars R' ∘ₗ e.symm.toLinearMap
    have hΦ : relationSpan I g M ≤
        LinearMap.ker (Φ.lTensor (I.map (algebraMap R R'))) := by
      rw [relationSpan, Submodule.span_le]
      rintro t ⟨z, hz, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sum, LinearMap.lTensor_tmul]
      have hΦz : ∀ k, Φ ((1 : R') ⊗ₜ[R] z k) = f (z k) := fun k ↦ he (z k)
      simp only [hΦz]
      exact htor r g z hz
    have h0 := hΦ hmem
    rw [LinearMap.mem_ker, map_sum] at h0
    simpa [Φ] using h0
  refine ⟨rTensor_injective_of_relations _ (mapGen I g) hg'
    fun x hx ↦ relations_of_isLocalizedModule _ (mapGen I g) W ψ hrelP x hx, ?_⟩
  -- Flatness modulo `I R'`.
  have : Module.Flat (R' ⧸ I.map (algebraMap R R'))
      ((R' ⧸ I.map (algebraMap R R')) ⊗[R'] ((S ⊗[R] R') ⊗[S] M)) := by
    let e₁ := TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (R' ⧸ I.map (algebraMap R R')) (R' ⧸ I.map (algebraMap R R'))) e
    let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange R R'
      (R' ⧸ I.map (algebraMap R R')) (R' ⧸ I.map (algebraMap R R')) M
    let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I)
      (R' ⧸ I.map (algebraMap R R')) (R' ⧸ I.map (algebraMap R R')) M
    exact Module.Flat.of_linearEquiv (e₁ ≪≫ₗ e₂ ≪≫ₗ e₃.symm)
  exact flat_of_isLocalizedModule _ (mapGen I g) W ψ hg'

end TensorKernelTransitionReduction

open TensorKernelTransitionReduction in
theorem tensorKernelTransitionReduction : TensorKernelTransitionReductionStatement :=
  fun R R' S S' M M' ↦ @reduction R R' S S' M M'

end Langlands.Algebra
