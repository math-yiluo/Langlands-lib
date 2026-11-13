import Langlands.Representation.Unitary.AdmissibleOrthogonalComplementStatement
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof

/-!
# The orthogonal of an invariant subspace (Renard IV.2.2, Proposition): proof

The orthogonal `V₁^⊥` of a `G`-stable subspace `V₁` is `G`-stable by invariance of the
form, meets `V₁` trivially by positive definiteness, and together with `V₁` spans `V`:
the functional `s ↦ b(v, s)` on the admissible subrepresentation `V₁` is represented by
some `s₀ ∈ V₁` (smooth-dual surjectivity), and then `v - s₀ ∈ V₁^⊥`.
-/

namespace Langlands

universe uG uV

/-- Renard IV.2.2, Proposition: for an admissible representation with an invariant
positive definite Hermitian form `b`, the orthogonal of a `G`-stable subspace `V₁` is a
`G`-stable subspace complementary to `V₁`. -/
theorem admissibleUnitaryOrthogonalComplement :
    AdmissibleUnitaryOrthogonalComplementStatement.{uG, uV} := by
  intro G _ _ _ hcofinal V _ _ ρ hρ b V₁ hV₁
  let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
  -- `V₁` as a subrepresentation of `ρ`.
  let S : Subrepresentation ρ :=
    { toSubmodule := V₁
      apply_mem_toSubmodule := fun g _ hv => hV₁ g _ hv }
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hi : Function.Injective i := Subtype.val_injective
  have hS : IsAdmissible S.toRepresentation := isAdmissible_of_injective i hi hρ
  let bS := b.comap i hi
  -- The orthogonal of `V₁` as a submodule.
  let W : Submodule ℂ V :=
    { carrier := {v | ∀ v₁ ∈ V₁, b.inner v v₁ = 0}
      zero_mem' := fun v₁ _ => InnerProductSpace.Core.inner_zero_left v₁
      add_mem' := by
        intro v w hv hw v₁ hv₁
        rw [b.add_left, hv v₁ hv₁, hw v₁ hv₁, zero_add]
      smul_mem' := by
        intro c v hv v₁ hv₁
        rw [b.smul_left, hv v₁ hv₁, mul_zero] }
  have hWinv : ∀ (g : G), ∀ v ∈ W, ρ g v ∈ W := by
    intro g v hv v₁ hv₁
    have hs : ρ g⁻¹ v₁ ∈ V₁ := hV₁ g⁻¹ v₁ hv₁
    rw [← Representation.self_inv_apply ρ g v₁, b.invariant]
    exact hv _ hs
  -- Every vector is an element of `V₁` plus an element of `W`.
  have hdecomp (v : V) : ∃ s : V₁, v - (s : V) ∈ W := by
    let ℓ : SmoothDual S.toRepresentation :=
      contragredientMap i (b.toSmoothDual hρ.1 v)
    obtain ⟨s, hs⟩ := bS.toSmoothDual_surjective hcofinal hS ℓ
    refine ⟨s, fun t ht => ?_⟩
    have heq := congrArg
      (fun f : SmoothDual S.toRepresentation =>
        smoothDualPairing S.toRepresentation f ⟨t, ht⟩) hs
    change b.inner (s : V) t = b.inner v t at heq
    change b.inner (v - (s : V)) t = 0
    rw [InnerProductSpace.Core.inner_sub_left, heq, sub_self]
  refine ⟨W, rfl, hWinv, ?_, ?_⟩
  · rw [disjoint_iff, eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    rw [Submodule.mem_bot]
    exact b.definite v (hv.2 v hv.1)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨s, hs⟩ := hdecomp v
    have hsum : (s : V) + (v - (s : V)) ∈ V₁ ⊔ W :=
      Submodule.add_mem_sup s.property hs
    simpa only [add_sub_cancel] using hsum

end Langlands
