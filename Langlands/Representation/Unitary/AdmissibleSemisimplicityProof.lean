import Langlands.Representation.Unitary.AdmissibleSemisimplicityStatement
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-!
# Algebraic semisimplicity from an admissible positive invariant form

Every invariant subspace has an invariant orthogonal complement. Admissibility
and smooth-dual surjectivity supply the algebraic orthogonal decomposition.
-/

namespace Langlands

universe uG uV

/-- An admissible unitarizable representation is algebraically semisimple
when compact open subgroups are cofinal among open subgroups. -/
theorem admissibleUnitarySemisimplicity :
    AdmissibleUnitarySemisimplicityStatement.{uG, uV} := by
  intro G _ _ _ hcofinal V _ _ ρ hρ hunitary
  obtain ⟨b⟩ := hunitary
  let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
  constructor
  intro S
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hi : Function.Injective i := Subtype.val_injective
  have hS : IsAdmissible S.toRepresentation := isAdmissible_of_injective i hi hρ
  let bS := b.comap i hi
  let C : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {v | ∀ s : S.toSubmodule, b.inner v s = 0}
          zero_mem' := fun s => InnerProductSpace.Core.inner_zero_left (s : V)
          add_mem' := by
            intro v w hv hw s
            rw [b.add_left, hv s, hw s, zero_add]
          smul_mem' := by
            intro c v hv s
            rw [b.smul_left, hv s, mul_zero] }
      apply_mem_toSubmodule := by
        intro g v hv s
        have hs : ρ g⁻¹ (s : V) ∈ S.toSubmodule :=
          S.apply_mem_toSubmodule g⁻¹ s.property
        rw [← Representation.self_inv_apply ρ g (s : V), b.invariant]
        exact hv ⟨_, hs⟩ }
  have hdecomp (v : V) : ∃ s : S.toSubmodule, v - (s : V) ∈ C.toSubmodule := by
    let ℓ : SmoothDual S.toRepresentation :=
      contragredientMap i (b.toSmoothDual hρ.1 v)
    obtain ⟨s, hs⟩ := bS.toSmoothDual_surjective hcofinal hS ℓ
    refine ⟨s, fun t => ?_⟩
    have heq := congrArg
      (fun f : SmoothDual S.toRepresentation => smoothDualPairing S.toRepresentation f t) hs
    change b.inner (s : V) (t : V) = b.inner v (t : V) at heq
    change b.inner (v - (s : V)) (t : V) = 0
    rw [InnerProductSpace.Core.inner_sub_left, heq, sub_self]
  refine ⟨C, ?_, ?_⟩
  · intro U hUS hUC v hv
    change v = 0
    exact b.definite v (hUC hv ⟨v, hUS hv⟩)
  · intro U hSU hCU v _
    obtain ⟨s, hs⟩ := hdecomp v
    have hsum : (s : V) + (v - (s : V)) ∈ U.toSubmodule :=
      U.toSubmodule.add_mem (hSU s.property) (hCU hs)
    change v ∈ U.toSubmodule
    simpa only [sub_eq_add_neg, add_left_comm, add_neg_cancel, add_zero] using hsum

end Langlands
