import Langlands.Representation.Smooth.Contragredient.Definitions

/-! # Smooth contragredient laws: proposition target -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]

/-- Smoothness, invariant pairing, contravariance, and natural bidual evaluation. -/
def SmoothContragredientLawsStatement : Prop :=
  ∀ [IsTopologicalGroup G],
    (∀ ρ : Representation R G V, IsSmooth (smoothContragredient ρ)) ∧
    (∀ (ρ : Representation R G V) (g : G) (ℓ : SmoothDual ρ) (v : V),
      smoothDualPairing ρ (smoothContragredient ρ g ℓ) v =
        smoothDualPairing ρ ℓ (ρ g⁻¹ v)) ∧
    (∀ (ρ : Representation R G V) (g : G) (ℓ : SmoothDual ρ) (v : V),
      smoothDualPairing ρ (smoothContragredient ρ g ℓ) (ρ g v) =
        smoothDualPairing ρ ℓ v) ∧
    (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (f : ρ.IntertwiningMap σ) (ℓ : SmoothDual σ) (v : V),
      smoothDualPairing ρ (contragredientMap f ℓ) v = smoothDualPairing σ ℓ (f v)) ∧
    (∀ ρ : Representation R G V,
      contragredientMap (Representation.IntertwiningMap.id ρ) =
        Representation.IntertwiningMap.id (smoothContragredient ρ)) ∧
    (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (τ : Representation R G U) (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ),
      contragredientMap (g.comp f) = (contragredientMap f).comp (contragredientMap g)) ∧
    (∀ (ρ : Representation R G V) (hρ : IsSmooth ρ) (v : V) (ℓ : SmoothDual ρ),
      smoothDualPairing (smoothContragredient ρ) (smoothBidual hρ v) ℓ =
        smoothDualPairing ρ ℓ v) ∧
    (∀ (ρ : Representation R G V) (σ : Representation R G W)
      (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : ρ.IntertwiningMap σ),
      (contragredientMap (contragredientMap f)).comp (smoothBidual hρ) =
        (smoothBidual hσ).comp f)

end Langlands
