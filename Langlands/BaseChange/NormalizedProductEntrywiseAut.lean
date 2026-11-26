import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.Representation.Induction.SmoothGroupTransport
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-! # Entrywise pullback of normalized parabolic induction -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

universe u v uV

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)

/-- Pulling back the whole Levi tensor action agrees with pulling back each factor. -/
theorem blockTensor_comp_leviAut {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (V i)) :
    (B.blockTensor ρ).comp (leviAut σ B).toMonoidHom =
      B.blockTensor (fun i => (ρ i).comp (entrywiseAut σ (B.size i)).toMonoidHom) := by
  apply MonoidHom.ext
  intro m
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  exact (B.blockTensor_tprod ρ (leviAut σ B m) x).trans
    (B.blockTensor_tprod (fun i => (ρ i).comp
      (entrywiseAut σ (B.size i)).toMonoidHom) m x).symm

section Topology

variable [TopologicalSpace F] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [IsModuleTopology F E]

local notation "T" => LocalFieldData.ofInstances E

/-- Precomposition on sections transports actual normalized induction under an entrywise field automorphism. -/
def normalizedParabolicInducedEntrywiseAutEquiv {X : Type uV} [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X) :
    Representation.Equiv
      (((T).normalizedParabolicInduced B Ξ).comp (entrywiseAut σ n).toMonoidHom)
      ((T).normalizedParabolicInduced B (Ξ.comp (leviAut σ B).toMonoidHom)) := by
  apply Induction.precomposeSmoothInducedGroupEquiv
    (GeneralLinear.fieldEquiv n σ.toRingEquiv (continuous_algEquiv σ) (continuous_algEquiv σ.symm))
    (parabolicAut σ B) (fun _ => rfl)
  intro p
  apply LinearMap.ext
  intro x
  change ((T).parabolicHalfModulus B (parabolicAut σ B p) : ℂ) •
      Ξ (B.leviProjection E (parabolicAut σ B p)) x =
    ((T).parabolicHalfModulus B p : ℂ) • Ξ (leviAut σ B (B.leviProjection E p)) x
  rw [parabolicHalfModulus_parabolicAut, leviProjection_parabolicAut]

/-- The pulled-back normalized product is the actual normalized product of the pulled-back factors. -/
def normalizedProductInducedEntrywiseAutEquiv {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (V i)) :
    Representation.Equiv
      (((T).normalizedProductInduced B ρ).comp (entrywiseAut σ n).toMonoidHom)
      ((T).normalizedProductInduced B
        (fun i => (ρ i).comp (entrywiseAut σ (B.size i)).toMonoidHom)) := by
  apply (congrArg (fun Ξ => Representation.Equiv
    (((T).normalizedProductInduced B ρ).comp (entrywiseAut σ n).toMonoidHom)
    ((T).normalizedParabolicInduced B Ξ)) (blockTensor_comp_leviAut σ B ρ)).mp
  exact normalizedParabolicInducedEntrywiseAutEquiv σ B (B.blockTensor ρ)

end Topology

end Langlands.BaseChange
