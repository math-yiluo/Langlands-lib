import Langlands.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Smooth.Factorization.TwoFactorFixedVectorsProof
import Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
import Langlands.Representation.TensorProduct.MultiplicityCancellation
import Langlands.Representation.Smooth.SmoothPart.BasicProof

/-! # Admissibility and irreducibility of external tensor products -/

noncomputable section
open scoped TensorProduct

namespace Langlands.TwoFactorExternalTensor

open Representation
open TwoFactorExistence

universe uG₁ uG₂ uV₁ uV₂ uI

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
variable {V₁ : Type uV₁} {V₂ : Type uV₂}
variable [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

abbrev external (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂) :=
  MixedProductTensor.external ρ₁ ρ₂

variable (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂)

/-- Stability under the first group extends to its group algebra. -/
theorem algebra_first_mem (N : Subrepresentation (external ρ₁ ρ₂))
    (r : MonoidAlgebra ℂ G₁) {t : V₁ ⊗[ℂ] V₂} (ht : t ∈ N) :
    TensorProduct.map (ρ₁.asAlgebraHom r) LinearMap.id t ∈ N := by
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
    simp only [map_zero, TensorProduct.map_zero_left, LinearMap.zero_apply]
    exact N.toSubmodule.zero_mem
  | add a b ha hb =>
    simp only [map_add, TensorProduct.map_add_left, LinearMap.add_apply]
    exact N.toSubmodule.add_mem ha hb
  | single g a =>
    simp only [asAlgebraHom_single, TensorProduct.map_smul_left, LinearMap.smul_apply]
    apply N.toSubmodule.smul_mem a
    simpa [external, MixedProductTensor.external, Representation.tprod_apply, Module.End.one_eq_id] using
      N.apply_mem_toSubmodule (g, 1) ht

/-- Density on the finitely many coefficients of a tensor makes every first
linear endomorphism preserve a product subrepresentation. -/
theorem map_first_mem [ρ₁.IsIrreducible]
    (hS : ∀ f : ρ₁.IntertwiningMap ρ₁, ∃ c : ℂ, f = c • IntertwiningMap.id ρ₁)
    (N : Subrepresentation (external ρ₁ ρ₂)) (f : V₁ →ₗ[ℂ] V₁)
    {t : V₁ ⊗[ℂ] V₂} (ht : t ∈ N) :
    TensorProduct.map f LinearMap.id t ∈ N := by
  classical
  let b := Module.Free.chooseBasis ℂ V₂
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right b t
  obtain ⟨r, hr⟩ := exists_algebra_eq ρ₁ hS f (c.support.image c)
  have heq : TensorProduct.map f LinearMap.id (c.sum fun i v => v ⊗ₜ b i) =
      TensorProduct.map (ρ₁.asAlgebraHom r) LinearMap.id (c.sum fun i v => v ⊗ₜ b i) := by
    simp only [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [hr (c i) (Finset.mem_image_of_mem c hi)]
  rw [heq]
  exact algebra_first_mem ρ₁ ρ₂ N r ht

/-- A rank-one endomorphism extracts a coefficient as a pure tensor. -/
theorem map_rank_one {I : Type uI} [DecidableEq I] (b : Module.Basis I ℂ V₁)
    (i : I) (v : V₁) (t : V₁ ⊗[ℂ] V₂) :
    TensorProduct.map ((b.coord i).smulRight v) LinearMap.id t =
      v ⊗ₜ TensorProduct.equivFinsuppOfBasisLeft b t i := by
  induction t with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.smulRight_apply, LinearMap.id_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, TensorProduct.smul_tmul,
      TensorProduct.tmul_smul, Module.Basis.coord_apply]
  | add t s ht hs => simp [ht, hs, TensorProduct.tmul_add]

def firstSlice (N : Subrepresentation (external ρ₁ ρ₂)) (w : V₂) :
    Subrepresentation ρ₁ where
  toSubmodule := N.toSubmodule.comap ((TensorProduct.mk ℂ V₁ V₂).flip w)
  apply_mem_toSubmodule g v hv := by
    simpa [external, MixedProductTensor.external, Representation.tprod_apply] using
      N.apply_mem_toSubmodule (g, 1) hv

def secondSlice (N : Subrepresentation (external ρ₁ ρ₂)) (v : V₁) :
    Subrepresentation ρ₂ where
  toSubmodule := N.toSubmodule.comap (TensorProduct.mk ℂ V₁ V₂ v)
  apply_mem_toSubmodule g w hw := by
    simpa [external, MixedProductTensor.external, Representation.tprod_apply] using
      N.apply_mem_toSubmodule (1, g) hw

/-- A nonzero product subrepresentation contains a nonzero pure tensor. -/
theorem exists_pure_mem [ρ₁.IsIrreducible]
    (hS : ∀ f : ρ₁.IntertwiningMap ρ₁, ∃ c : ℂ, f = c • IntertwiningMap.id ρ₁)
    (N : Subrepresentation (external ρ₁ ρ₂)) (hN : N ≠ ⊥) :
    ∃ v : V₁, ∃ w : V₂, v ≠ 0 ∧ w ≠ 0 ∧ v ⊗ₜ w ∈ N := by
  classical
  obtain ⟨t, ht, ht0⟩ := exists_ne_zero_of_ne_bot hN
  let b := Module.Free.chooseBasis ℂ V₁
  obtain ⟨i, hi⟩ : ∃ i, TensorProduct.equivFinsuppOfBasisLeft b t i ≠ 0 := by
    by_contra h
    apply ht0
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    have hz : TensorProduct.equivFinsuppOfBasisLeft b t = 0 :=
      Finsupp.ext fun i => not_not.mp (not_exists.mp h i)
    simpa using hz
  refine ⟨b i, TensorProduct.equivFinsuppOfBasisLeft b t i, b.ne_zero i, hi, ?_⟩
  rw [← map_rank_one]
  exact map_first_mem ρ₁ ρ₂ hS N _ ht

/-- Density and irreducibility of the two factors imply irreducibility of the
external tensor representation. -/
theorem irreducible [ρ₁.IsIrreducible] [ρ₂.IsIrreducible]
    (hS : ∀ f : ρ₁.IntertwiningMap ρ₁, ∃ c : ℂ, f = c • IntertwiningMap.id ρ₁) :
    (external ρ₁ ρ₂).IsIrreducible := by
  let : Nontrivial V₁ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G₁) ρ₁.asModule
  let : Nontrivial V₂ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G₂) ρ₂.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V₁)
  obtain ⟨y, hy⟩ := exists_ne (0 : V₂)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun N => ?_ }
  · have hm := mem_top (σ := external ρ₁ ρ₂) (x ⊗ₜ y)
    rw [← h] at hm
    exact TensorMultiplicity.tmul_ne_zero hx hy (mem_bot_iff.mp hm)
  · by_cases hN : N = ⊥
    · exact Or.inl hN
    right
    obtain ⟨v, w, hv, hw, hvw⟩ := exists_pure_mem ρ₁ ρ₂ hS N hN
    have hs₂ : secondSlice ρ₁ ρ₂ N v = ⊤ := by
      apply (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
      intro h
      have hm : w ∈ secondSlice ρ₁ ρ₂ N v := hvw
      rw [h] at hm
      exact hw (mem_bot_iff.mp hm)
    have hAll : ∀ z : V₂, v ⊗ₜ z ∈ N := by
      intro z
      change z ∈ secondSlice ρ₁ ρ₂ N v
      rw [hs₂]
      exact mem_top z
    have hs₁ (z : V₂) : firstSlice ρ₁ ρ₂ N z = ⊤ := by
      apply (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
      intro h
      have hm : v ∈ firstSlice ρ₁ ρ₂ N z := hAll z
      rw [h] at hm
      exact hv (mem_bot_iff.mp hm)
    apply eq_top_of_forall
    intro t
    induction t with
    | tmul a b =>
      change a ∈ firstSlice ρ₁ ρ₂ N b
      rw [hs₁]
      exact mem_top a
    | add t s ht hs => exact N.toSubmodule.add_mem ht hs

section Topology

variable [TopologicalSpace G₁] [TopologicalSpace G₂]

theorem smooth (h₁ : IsSmooth ρ₁) (h₂ : IsSmooth ρ₂) :
    IsSmooth (external ρ₁ ρ₂) := by
  intro t
  induction t with
  | tmul v w =>
    obtain ⟨K₁, hK₁⟩ := h₁ v
    obtain ⟨K₂, hK₂⟩ := h₂ w
    refine ⟨K₁.prod K₂, ?_⟩
    intro g
    change ρ₁ g.val.1 v ⊗ₜ ρ₂ g.val.2 w = v ⊗ₜ w
    exact congrArg₂ (fun v w => v ⊗ₜ[ℂ] w)
      (hK₁ ⟨g.val.1, g.property.1⟩) (hK₂ ⟨g.val.2, g.property.2⟩)
  | add t s ht hs => exact isSmoothVector_add ht hs

theorem admissible (h₁ : IsAdmissible ρ₁) (h₂ : IsAdmissible ρ₂) :
    IsAdmissible (external ρ₁ ρ₂) := by
  refine ⟨smooth ρ₁ ρ₂ h₁.1 h₂.1, fun K => ?_⟩
  let K₁ := K.comap (MonoidHom.inl G₁ G₂) continuous_inl'
  let K₂ := K.comap (MonoidHom.inr G₁ G₂) continuous_inr'
  have hprod : K₁.toSubgroup.prod K₂.toSubgroup ≤ K.toSubgroup := by
    intro g hg
    simpa using K.mul_mem hg.1 hg.2
  let P := fixedVectors ρ₁ K₁.toSubgroup
  let Q := fixedVectors ρ₂ K₂.toSubgroup
  let i := TensorProduct.map P.subtype Q.subtype
  have := h₁.2 K₁
  have := h₂.2 K₂
  have hfin : Module.Finite ℂ (LinearMap.range i) := inferInstance
  have heq : LinearMap.range i =
      fixedVectors (external ρ₁ ρ₂) (K₁.toSubgroup.prod K₂.toSubgroup) :=
    (productFixedVectors G₁ G₂ V₁ V₂ ρ₁ ρ₂ K₁.toSubgroup K₂.toSubgroup).2
  rw [heq] at hfin
  have hle : fixedVectors (external ρ₁ ρ₂) K.toSubgroup ≤
      fixedVectors (external ρ₁ ρ₂) (K₁.toSubgroup.prod K₂.toSubgroup) := by
    intro t ht
    exact TwoFactorExistence.mem_fixedVectors_iff.mpr fun g hg =>
      TwoFactorExistence.mem_fixedVectors_iff.mp ht g (hprod hg)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end Topology
end Langlands.TwoFactorExternalTensor

namespace Langlands

universe uG₁ uG₂ uV₁ uV₂

/-- External tensors of admissible representations are admissible and are
irreducible when both factors are irreducible. -/
theorem admissibleExternalTensor :
    AdmissibleExternalTensorStatement.{uG₁, uG₂, uV₁, uV₂} := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ V₁ V₂ _ _ _ _ ρ₁ ρ₂ ha₁ ha₂
  refine ⟨TwoFactorExternalTensor.admissible ρ₁ ρ₂ ha₁ ha₂, ?_⟩
  intro hi₁ hi₂
  let := hi₁
  let := hi₂
  exact TwoFactorExternalTensor.irreducible ρ₁ ρ₂ fun f =>
    (admissibleSchur_scalarEndomorphism ρ₁ ha₁ hi₁ f).exists

end Langlands
