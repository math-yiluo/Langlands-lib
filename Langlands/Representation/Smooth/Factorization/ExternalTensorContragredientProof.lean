import Langlands.Representation.Smooth.Factorization.ExternalTensorContragredientStatement
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-! # The contragredient of a binary external tensor product -/

noncomputable section

open scoped TensorProduct
open Module

namespace Langlands.ExternalTensorDual

universe uG₁ uG₂ uV₁ uV₂ uA uB

section Pairing

variable {V₁ : Type uV₁} {V₂ : Type uV₂} {A : Type uA} {B : Type uB}
variable [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

private theorem basis_eval_sum {ι : Type*} [Fintype ι] (b : Basis ι ℂ A)
    (e : A →ₗ[ℂ] ℂ) (a : A) :
    ∑ i, e (b i) * b.coord i a = e a := by
  have h := congrArg e (b.sum_repr a)
  simpa only [map_sum, map_smul, Basis.coord_apply, smul_eq_mul, mul_comm] using h

private theorem tensorPairing_injective
    (f : A →ₗ[ℂ] Module.Dual ℂ V₁) (g : B →ₗ[ℂ] Module.Dual ℂ V₂)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective
      ((TensorProduct.dualDistrib ℂ V₁ V₂).comp (TensorProduct.map f g)) := by
  classical
  let b := Basis.ofVectorSpace ℂ A
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := B) b
  let C (v : V₂) : A ⊗[ℂ] B →ₗ[ℂ] A :=
    (TensorProduct.rid ℂ A).toLinearMap.comp
      (TensorProduct.map LinearMap.id (g.flip v))
  have hC (x : A ⊗[ℂ] B) (v₁ : V₁) (v₂ : V₂) :
      f (C v₂ x) v₁ =
        TensorProduct.dualDistrib ℂ V₁ V₂ (TensorProduct.map f g x)
          (v₁ ⊗ₜ v₂) := by
    induction x with
    | tmul a d => simp [C, mul_comm]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  have hcoord (x : A ⊗[ℂ] B) (i : Basis.ofVectorSpaceIndex ℂ A) (v : V₂) :
      g (E x i) v = b.coord i (C v x) := by
    induction x with
    | tmul a d =>
      simp [E, C, mul_comm]
    | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, LinearMap.add_apply, hx, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hc (v : V₂) : C v x = 0 := by
    apply hf
    ext v₁
    rw [hC]
    simpa using congrArg
      (fun φ : Module.Dual ℂ (V₁ ⊗[ℂ] V₂) => φ (v₁ ⊗ₜ v)) hx
  apply E.injective
  ext i
  change E x i = 0
  apply hg
  ext v
  rw [hcoord, hc]
  simp

end Pairing

section Representations

variable {G₁ : Type uG₁} {G₂ : Type uG₂} [Group G₁] [Group G₂]
variable [TopologicalSpace G₁] [TopologicalSpace G₂]
variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
variable {V₁ : Type uV₁} {V₂ : Type uV₂}
variable [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

private abbrev external (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂) :=
  Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂))
    (ρ₂.comp (MonoidHom.snd G₁ G₂))

omit [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] in
private theorem external_smooth (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂) (h₁ : IsSmooth ρ₁) (h₂ : IsSmooth ρ₂) :
    IsSmooth (external ρ₁ ρ₂) := by
  intro x
  induction x with
  | tmul v₁ v₂ =>
    obtain ⟨K₁, hK₁⟩ := h₁ v₁
    obtain ⟨K₂, hK₂⟩ := h₂ v₂
    refine ⟨K₁.prod K₂, ?_⟩
    intro k
    change ρ₁ k.val.1 v₁ ⊗ₜ ρ₂ k.val.2 v₂ = v₁ ⊗ₜ v₂
    exact congrArg₂ (fun a b => a ⊗ₜ[ℂ] b)
      (hK₁ ⟨k.val.1, k.property.1⟩) (hK₂ ⟨k.val.2, k.property.2⟩)
  | add x y hx hy => exact (smoothVectors (external ρ₁ ρ₂)).add_mem hx hy

private def pairingIntertwiner (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂) :
    (external (smoothContragredient ρ₁) (smoothContragredient ρ₂)).IntertwiningMap
      (external ρ₁ ρ₂).dual where
  toLinearMap := (TensorProduct.dualDistrib ℂ V₁ V₂).comp
    (TensorProduct.map (smoothDualPairing ρ₁) (smoothDualPairing ρ₂))
  isIntertwining' k := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro ℓ₁
    apply LinearMap.ext
    intro ℓ₂
    apply TensorProduct.ext
    apply LinearMap.ext
    intro v₁
    apply LinearMap.ext
    intro v₂
    rfl

private def tensorMap (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂) :
    (external (smoothContragredient ρ₁) (smoothContragredient ρ₂)).IntertwiningMap
      (smoothContragredient (external ρ₁ ρ₂)) :=
  smoothLift (external_smooth _ _
    (isSmooth_smoothContragredient ρ₁) (isSmooth_smoothContragredient ρ₂))
    (pairingIntertwiner ρ₁ ρ₂)

private theorem pairingIntertwiner_apply (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂)
    (ℓ₁ : SmoothDual ρ₁) (ℓ₂ : SmoothDual ρ₂) (v₁ : V₁) (v₂ : V₂) :
    pairingIntertwiner ρ₁ ρ₂ (ℓ₁ ⊗ₜ ℓ₂) (v₁ ⊗ₜ v₂) =
      ℓ₁.val v₁ * ℓ₂.val v₂ := rfl

private theorem tensorMap_apply (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂)
    (ℓ₁ : SmoothDual ρ₁) (ℓ₂ : SmoothDual ρ₂) (v₁ : V₁) (v₂ : V₂) :
    (tensorMap ρ₁ ρ₂ (ℓ₁ ⊗ₜ ℓ₂)).val (v₁ ⊗ₜ v₂) = ℓ₁.val v₁ * ℓ₂.val v₂ := rfl

private theorem tensorMap_injective (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂) :
    Function.Injective (tensorMap ρ₁ ρ₂) := by
  intro x y h
  exact tensorPairing_injective (smoothDualPairing ρ₁) (smoothDualPairing ρ₂)
    Subtype.val_injective Subtype.val_injective (congrArg Subtype.val h)

set_option maxHeartbeats 800000 in
private theorem tensorMap_surjective (ρ₁ : Representation ℂ G₁ V₁)
    (ρ₂ : Representation ℂ G₂ V₂)
    (hcof : ∀ K : OpenSubgroup G₁, ∃ L : OpenSubgroup G₁,
      IsCompact (L : Set G₁) ∧ L ≤ K)
    (hρ₁ : IsAdmissible ρ₁) :
    Function.Surjective (tensorMap ρ₁ ρ₂) := by
  classical
  intro ℓ
  obtain ⟨U, hU⟩ := ℓ.property
  let K₁ := U.comap (MonoidHom.inl G₁ G₂) (continuous_id.prodMk continuous_const)
  let K₂ := U.comap (MonoidHom.inr G₁ G₂) (continuous_const.prodMk continuous_id)
  let q : V₂ →ₗ[ℂ] Module.Dual ℂ V₁ :=
    ((TensorProduct.mk ℂ V₁ V₂).compr₂ ℓ.val).flip
  have h₁ (k : K₁) (v₁ : V₁) (v₂ : V₂) :
      q v₂ (ρ₁ k.val⁻¹ v₁) = q v₂ v₁ := by
    have h := congrArg
      (fun f : Module.Dual ℂ (V₁ ⊗[ℂ] V₂) => f (v₁ ⊗ₜ v₂))
      (hU ⟨(k.val, 1), k.property⟩)
    change ℓ.val (ρ₁ k.val⁻¹ v₁ ⊗ₜ ρ₂ (1 : G₂)⁻¹ v₂) =
      ℓ.val (v₁ ⊗ₜ v₂) at h
    simpa [q] using h
  have h₂ (k : K₂) (v₁ : V₁) (v₂ : V₂) :
      q (ρ₂ k.val⁻¹ v₂) v₁ = q v₂ v₁ := by
    have h := congrArg
      (fun f : Module.Dual ℂ (V₁ ⊗[ℂ] V₂) => f (v₁ ⊗ₜ v₂))
      (hU ⟨(1, k.val), k.property⟩)
    change ℓ.val (ρ₁ (1 : G₁)⁻¹ v₁ ⊗ₜ ρ₂ k.val⁻¹ v₂) =
      ℓ.val (v₁ ⊗ₜ v₂) at h
    simpa [q] using h
  let qS : V₂ →ₗ[ℂ] SmoothDual ρ₁ :=
    q.codRestrict (smoothVectors ρ₁.dual) (by
      intro v₂
      refine ⟨K₁, ?_⟩
      intro k
      exact LinearMap.ext (fun v₁ => h₁ k v₁ v₂))
  let F := fixedVectors (smoothContragredient ρ₁) K₁.toSubgroup
  let c : V₂ →ₗ[ℂ] F := qS.codRestrict F (by
    intro v₂ k
    apply Subtype.ext
    exact LinearMap.ext (fun v₁ => h₁ k v₁ v₂))
  have hc (k : K₂) (v₂ : V₂) : c (ρ₂ k.val⁻¹ v₂) = c v₂ := by
    apply Subtype.ext
    apply Subtype.ext
    exact LinearMap.ext (fun v₁ => h₂ k v₁ v₂)
  let : Module.Finite ℂ F :=
    (isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ₁ hρ₁).2 K₁
  let : Module.Free ℂ F := Module.Free.of_divisionRing ℂ F
  let b := Module.finBasis ℂ F
  let r (i : Fin (Module.finrank ℂ F)) : SmoothDual ρ₂ :=
    ⟨(b.coord i).comp c, ⟨K₂, by
      intro k
      apply LinearMap.ext
      intro v₂
      change b.coord i (c (ρ₂ k.val⁻¹ v₂)) = b.coord i (c v₂)
      rw [hc]⟩⟩
  refine ⟨∑ i, (b i).val ⊗ₜ r i, ?_⟩
  apply Subtype.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v₁
  apply LinearMap.ext
  intro v₂
  change pairingIntertwiner ρ₁ ρ₂ (∑ i, (b i).val ⊗ₜ r i) (v₁ ⊗ₜ v₂) =
    ℓ.val (v₁ ⊗ₜ v₂)
  simp only [map_sum, LinearMap.sum_apply]
  simp only [pairingIntertwiner_apply]
  have hr (i : Fin (Module.finrank ℂ F)) :
      (r i).val v₂ = b.coord i (c v₂) := rfl
  simp_rw [hr]
  exact basis_eval_sum b (((smoothDualPairing ρ₁).flip v₁).comp F.subtype) (c v₂)

end Representations

end ExternalTensorDual

/-- Renard III.1.14, second assertion: the canonical pairing identifies the
external tensor of the smooth contragredients with the smooth contragredient
of the external tensor product. -/
theorem admissibleExternalTensorContragredient.{uG₁, uG₂, uV₁, uV₂} :
    AdmissibleExternalTensorContragredientStatement.{uG₁, uG₂, uV₁, uV₂} := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ V₁ V₂ _ _ _ _ ρ₁ ρ₂ h₁ _
  have hcof : ∀ K : OpenSubgroup G₁, ∃ L : OpenSubgroup G₁,
      IsCompact (L : Set G₁) ∧ L ≤ K := by
    intro K
    exact ((Topology.LocallyProfiniteProof.vanDantzig G₁).1
      Topology.isLocallyProfinite_of_mathlib).2 (K : Set G₁) K.mem_nhds_one
  let e := (ExternalTensorDual.tensorMap ρ₁ ρ₂).ofBijective
    ⟨ExternalTensorDual.tensorMap_injective ρ₁ ρ₂,
      ExternalTensorDual.tensorMap_surjective ρ₁ ρ₂ hcof h₁⟩
  exact ⟨e, fun ℓ₁ ℓ₂ v₁ v₂ =>
    ExternalTensorDual.tensorMap_apply ρ₁ ρ₂ ℓ₁ ℓ₂ v₁ v₂⟩

end Langlands
