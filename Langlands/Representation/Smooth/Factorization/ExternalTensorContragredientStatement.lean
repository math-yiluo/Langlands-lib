import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.RepresentationTheory.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The contragredient of an external tensor product (Renard III.1.14, Proposition)

For admissible smooth representations `π₁`, `π₂` of t.d. groups `G₁`, `G₂`, the smooth
contragredient of `π₁ ⊠ π₂` is `π̃₁ ⊠ π̃₂`, through `ℓ₁ ⊗ ℓ₂ ↦ (v₁ ⊗ v₂ ↦ ℓ₁(v₁) ℓ₂(v₂))`.
-/

namespace Langlands

universe uG₁ uG₂ uV₁ uV₂

/-- Renard III.1.14, Proposition, second assertion (two factors): for admissible
representations `ρ₁`, `ρ₂` of t.d. groups `G₁`, `G₂`, the external tensor product
`ρ̃₁ ⊠ ρ̃₂` of the smooth contragredients is equivalent to the smooth contragredient of
`ρ₁ ⊠ ρ₂`, by an equivalence sending `ℓ₁ ⊗ ℓ₂` to the functional
`v₁ ⊗ v₂ ↦ ℓ₁(v₁) ℓ₂(v₂)`. -/
def AdmissibleExternalTensorContragredientStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
    (V₁ : Type uV₁) (V₂ : Type uV₂)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂),
    IsAdmissible ρ₁ → IsAdmissible ρ₂ →
    let ρ := Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂))
      (ρ₂.comp (MonoidHom.snd G₁ G₂))
    let ρ' := Representation.tprod ((smoothContragredient ρ₁).comp (MonoidHom.fst G₁ G₂))
      ((smoothContragredient ρ₂).comp (MonoidHom.snd G₁ G₂))
    ∃ e : ρ'.Equiv (smoothContragredient ρ),
      ∀ (ℓ₁ : SmoothDual ρ₁) (ℓ₂ : SmoothDual ρ₂) (v₁ : V₁) (v₂ : V₂),
        smoothDualPairing ρ (e (ℓ₁ ⊗ₜ ℓ₂)) (v₁ ⊗ₜ v₂) =
          smoothDualPairing ρ₁ ℓ₁ v₁ * smoothDualPairing ρ₂ ℓ₂ v₂

end Langlands
