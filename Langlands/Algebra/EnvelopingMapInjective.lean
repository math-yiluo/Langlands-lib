import Langlands.Algebra.EnvelopingFixedWeightDecomposition
import Mathlib.Order.Fin.Basic

/-! # Injective Lie algebra homomorphisms induce injective maps of enveloping algebras -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {L₁ : Type v} [LieRing L₁] [LieAlgebra k L₁]
  {L₂ : Type w} [LieRing L₂] [LieAlgebra k L₂]

/-- A basis of `L₂` beginning with the images of a basis of `L₁` under an injective Lie algebra
homomorphism. -/
def extendedBasis [FiniteDimensional k L₂] {m : ℕ} (b₁ : Module.Basis (Fin m) k L₁)
    (f : L₁ →ₗ⁅k⁆ L₂) (hf : Function.Injective f) (W : Submodule k L₂)
    (hW : IsCompl (LinearMap.range f.toLinearMap) W) :
    Module.Basis (Fin (m + Module.finrank k W)) k L₂ :=
  (((b₁.map (LinearEquiv.ofInjective f.toLinearMap hf)).prod (Module.finBasis k W)).map
    (Submodule.prodEquivOfIsCompl _ W hW)).reindex finSumFinEquiv

theorem extendedBasis_castAdd [FiniteDimensional k L₂] {m : ℕ}
    (b₁ : Module.Basis (Fin m) k L₁) (f : L₁ →ₗ⁅k⁆ L₂) (hf : Function.Injective f)
    (W : Submodule k L₂) (hW : IsCompl (LinearMap.range f.toLinearMap) W) (i : Fin m) :
    extendedBasis b₁ f hf W hW (Fin.castAdd (Module.finrank k W) i) = f (b₁ i) := by
  simp [extendedBasis, Module.Basis.reindex_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

/-- An injective homomorphism of Lie algebras over a field, with finite-dimensional source and
target, induces an injective homomorphism of enveloping algebras. -/
theorem lift_comp_injective [FiniteDimensional k L₁] [FiniteDimensional k L₂]
    (f : L₁ →ₗ⁅k⁆ L₂) (hf : Function.Injective f) :
    Function.Injective
      (UniversalEnvelopingAlgebra.lift k ((UniversalEnvelopingAlgebra.ι k).comp f)) := by
  classical
  let b₁ := Module.finBasis k L₁
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range f.toLinearMap)
  let r := Module.finrank k W
  let b₂ := extendedBasis b₁ f hf W hW
  let φ := UniversalEnvelopingAlgebra.lift k ((UniversalEnvelopingAlgebra.ι k).comp f)
  let ψ : Fin (Module.finrank k L₁) ↪o Fin (Module.finrank k L₁ + r) := Fin.castAddOrderEmb r
  let ext : (Fin (Module.finrank k L₁) → ℕ) → (Fin (Module.finrank k L₁ + r) → ℕ) :=
    fun e => Function.extend ψ e 0
  have hext_inj : Function.Injective ext := by
    intro e e' h
    funext j
    have := congrFun h (ψ j)
    simpa [ext, ψ.injective.extend_apply] using this
  have hmon (e : Fin (Module.finrank k L₁) → ℕ) :
      φ (orderedPBWMonomial b₁ e) = orderedPBWMonomial b₂ (ext e) := by
    have he_zero (i : Fin (Module.finrank k L₁ + r)) (hi : i ∉ Set.range ψ) : ext e i = 0 := by
      simp only [ext]
      rw [Function.extend_apply' _ _ _ (fun ⟨j, hj⟩ => hi ⟨j, hj⟩)]
      rfl
    rw [orderedPBWMonomial, orderedPBWMonomial, map_list_prod, List.map_ofFn,
      ofFn_prod_pow_orderEmbedding ψ _ (ext e) he_zero]
    congr 1
    refine congrArg List.ofFn (funext fun j => ?_)
    simp only [Function.comp_apply, map_pow, φ, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieHom.comp_apply, ext, ψ.injective.extend_apply]
    congr 2
    exact (extendedBasis_castAdd b₁ f hf W hW j).symm
  have hli : LinearIndependent k (φ ∘ orderedPBWBasisOf b₁) := by
    have h : φ ∘ orderedPBWBasisOf b₁ = orderedPBWBasisOf b₂ ∘ ext := by
      funext e
      simp only [Function.comp_apply, orderedPBWBasisOf_apply, hmon]
    rw [h]
    exact (orderedPBWBasisOf b₂).linearIndependent.comp ext hext_inj
  intro x y hxy
  have hinj : Function.Injective (φ.toLinearMap ∘ₗ
      (Finsupp.linearCombination k (orderedPBWBasisOf b₁))) := by
    rw [← Finsupp.linearCombination_linear_comp]
    exact hli
  have hx := (orderedPBWBasisOf b₁).linearCombination_repr x
  have hy := (orderedPBWBasisOf b₁).linearCombination_repr y
  have : (orderedPBWBasisOf b₁).repr x = (orderedPBWBasisOf b₁).repr y := by
    apply hinj
    simp only [LinearMap.coe_comp, Function.comp_apply, hx, hy, AlgHom.toLinearMap_apply]
    exact hxy
  exact (orderedPBWBasisOf b₁).repr.injective this

end Langlands.Algebra.UniversalEnveloping
