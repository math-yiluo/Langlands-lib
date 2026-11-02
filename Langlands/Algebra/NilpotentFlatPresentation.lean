import Langlands.Algebra.NilpotentModuleFiniteness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Equalizer

universe u v w z

open TensorProduct

namespace Langlands.Algebra

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- Reduction over an algebra agrees with reduction over its base ring. -/
noncomputable def reductionBaseEquiv (I : Ideal A) :
    ((B ⧸ I.map (algebraMap A B)) ⊗[B] M) ≃ₗ[A] (A ⧸ I) ⊗[A] M :=
by
  let P : Submodule B M := (I.map (algebraMap A B)) • (⊤ : Submodule B M)
  let e₁ : ((B ⧸ I.map (algebraMap A B)) ⊗[B] M) ≃ₗ[A] M ⧸ P :=
    (TensorProduct.quotTensorEquivQuotSMul M (I.map (algebraMap A B))).restrictScalars A
  let e₂ : (M ⧸ P) ≃ₗ[A] M ⧸ P.restrictScalars A :=
    (Submodule.Quotient.restrictScalarsEquiv A P).symm
  have h : P.restrictScalars A = I • (⊤ : Submodule A M) := by
    simp only [P, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  exact e₁ ≪≫ₗ e₂ ≪≫ₗ Submodule.quotEquivOfEq _ _ h ≪≫ₗ
    (TensorProduct.quotTensorEquivQuotSMul M I).symm

@[simp]
theorem reductionBaseEquiv_mk_tmul (I : Ideal A) (b : B) (m : M) :
    reductionBaseEquiv A B M I
        (Ideal.Quotient.mk (I.map (algebraMap A B)) b ⊗ₜ[B] m) =
      1 ⊗ₜ[A] (b • m) := by
  simp only [reductionBaseEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk]

variable {M}
variable {N : Type z} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

theorem reductionBaseEquiv_natural (I : Ideal A) (f : M →ₗ[B] N)
    (x : (B ⧸ I.map (algebraMap A B)) ⊗[B] M) :
    reductionBaseEquiv A B N I ((f.baseChange (B ⧸ I.map (algebraMap A B))) x) =
      (f.restrictScalars A).lTensor (A ⧸ I) (reductionBaseEquiv A B M I x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp
  | add x y hx hy => simp [hx, hy]


/-- Base-flat cokernels make reduction preserve the injection on the left,
even when the algebra is not flat over the base. -/
theorem reduction_injective_of_exact_of_base_flat
    {L : Type*} [AddCommGroup L] [Module A L] [Module B L] [IsScalarTower A B L]
    [Module.Flat A M] (I : Ideal A) (f : L →ₗ[B] M) (hf : Function.Surjective f)
    (g : N →ₗ[B] L) (hg : Function.Injective g) (H : Function.Exact g f) :
    Function.Injective (g.baseChange (B ⧸ I.map (algebraMap A B))) := by
  have h : Function.Injective ((g.restrictScalars A).lTensor (A ⧸ I)) :=
    LinearMap.lTensor_injective_of_exact_of_flat
      (f.restrictScalars A) hf (g.restrictScalars A) hg H (A ⧸ I)
  intro x y hxy
  apply (reductionBaseEquiv A B N I).injective
  apply h
  rw [← reductionBaseEquiv_natural, ← reductionBaseEquiv_natural, hxy]

/-- Finite presentation lifts across nilpotent base reduction for a module
flat over the base, with no flatness condition on the algebra. -/
theorem finitePresentation_of_base_nilpotent
    [Module.Flat A M] (I : Ideal A) (hI : IsNilpotent I)
    [Module.FinitePresentation (B ⧸ I.map (algebraMap A B))
      ((B ⧸ I.map (algebraMap A B)) ⊗[B] M)] :
    Module.FinitePresentation B M := by
  let J := I.map (algebraMap A B)
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    simp only [J, ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
  have : Module.Finite B ((B ⧸ J) ⊗[B] M) :=
    Module.Finite.trans (B ⧸ J) _
  have : Module.Finite B (M ⧸ (J • (⊤ : Submodule B M))) :=
    Module.Finite.equiv (TensorProduct.quotTensorEquivQuotSMul M J)
  have : Module.Finite B M := finite_of_quotient_smul_nilpotent J hJ
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' B M
  let K := LinearMap.ker f
  let g := K.subtype
  let f₀ := f.baseChange (B ⧸ J)
  let g₀ := g.baseChange (B ⧸ J)
  have hg₀ : Function.Injective g₀ :=
    reduction_injective_of_exact_of_base_flat A B I f hf g K.subtype_injective
      (LinearMap.exact_subtype_ker_map f)
  have hf₀ : Function.Surjective f₀ := LinearMap.baseChange_surjective (B ⧸ J) hf
  have H₀ : Function.Exact g₀ f₀ :=
    lTensor_exact (B ⧸ J) (LinearMap.exact_subtype_ker_map f) hf
  have hfg : (LinearMap.range g₀).FG := by
    rw [← LinearMap.exact_iff.mp H₀]
    exact Module.FinitePresentation.fg_ker f₀ hf₀
  have : Module.Finite (B ⧸ J) ((B ⧸ J) ⊗[B] K) := by
    have : Module.Finite (B ⧸ J) (LinearMap.range g₀) := Module.Finite.of_fg hfg
    exact Module.Finite.equiv (LinearEquiv.ofInjective g₀ hg₀).symm
  have : Module.Finite B ((B ⧸ J) ⊗[B] K) :=
    Module.Finite.trans (B ⧸ J) _
  have : Module.Finite B (K ⧸ (J • (⊤ : Submodule B K))) :=
    Module.Finite.equiv (TensorProduct.quotTensorEquivQuotSMul K J)
  have : Module.Finite B K := finite_of_quotient_smul_nilpotent J hJ
  exact Module.finitePresentation_of_free_of_surjective f hf (Module.Finite.iff_fg.mp inferInstance)


/-- Choose an actual finite free presentation after lifting finite presentation
through a nilpotent reduction of the base. The two ranks are not prescribed. -/
noncomputable def finiteFreePresentationOfBaseNilpotent
    [Module.Flat A M] (I : Ideal A) (hI : IsNilpotent I)
    [Module.FinitePresentation (B ⧸ I.map (algebraMap A B))
      ((B ⧸ I.map (algebraMap A B)) ⊗[B] M)] :
    Σ n : ℕ, Σ m : ℕ,
      {p : ((Fin n → B) →ₗ[B] M) × ((Fin m → B) →ₗ[B] (Fin n → B)) //
        Function.Surjective p.1 ∧ Function.Exact p.2 p.1} := by
  have : Module.FinitePresentation B M := finitePresentation_of_base_nilpotent A B I hI
  apply Classical.choice
  obtain ⟨n, m, f, g, hf, H⟩ := Module.FinitePresentation.exists_fin' B M
  exact ⟨⟨n, m, ⟨(f, g), hf, H⟩⟩⟩

end Langlands.Algebra
