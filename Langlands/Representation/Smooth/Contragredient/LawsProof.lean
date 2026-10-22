import Langlands.Representation.Smooth.Contragredient.LawsStatement

/-! # Smooth contragredient laws -/

namespace Langlands

universe uR uG uV uW uU

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable [AddCommGroup U] [Module R U]
variable {ρ : Representation R G V} {σ : Representation R G W}

theorem isSmooth_smoothContragredient (ρ : Representation R G V) :
    IsSmooth (V := SmoothDual ρ) (smoothContragredient ρ) := by
  intro ℓ
  rcases ℓ.property with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k
  exact Subtype.ext (hK k)

theorem smoothDualPairing_action (g : G) (ℓ : SmoothDual ρ) (v : V) :
    smoothDualPairing ρ (smoothContragredient ρ g ℓ) v =
      smoothDualPairing ρ ℓ (ρ g⁻¹ v) := rfl

theorem smoothDualPairing_invariant (g : G) (ℓ : SmoothDual ρ) (v : V) :
    smoothDualPairing ρ (smoothContragredient ρ g ℓ) (ρ g v) =
      smoothDualPairing ρ ℓ v := by
  rw [smoothDualPairing_action, ρ.inv_self_apply]

theorem contragredientMap_apply (f : ρ.IntertwiningMap σ) (ℓ : SmoothDual σ) (v : V) :
    smoothDualPairing ρ (contragredientMap f ℓ) v = smoothDualPairing σ ℓ (f v) := rfl

theorem contragredientMap_id :
    contragredientMap (Representation.IntertwiningMap.id ρ) =
      Representation.IntertwiningMap.id (smoothContragredient ρ) := by
  ext ℓ v
  rfl

theorem contragredientMap_comp {τ : Representation R G U}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    contragredientMap (g.comp f) = (contragredientMap f).comp (contragredientMap g) := by
  ext ℓ v
  rfl

theorem smoothBidual_apply (hρ : IsSmooth ρ) (v : V) (ℓ : SmoothDual ρ) :
    smoothDualPairing (smoothContragredient ρ) (smoothBidual hρ v) ℓ =
      smoothDualPairing ρ ℓ v := rfl

theorem smoothBidual_natural (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) :
    (contragredientMap (contragredientMap f)).comp (smoothBidual hρ) =
      (smoothBidual hσ).comp f := by
  ext v ℓ
  rfl

omit [IsTopologicalGroup G] in
theorem smoothContragredientLaws :
    SmoothContragredientLawsStatement (R := R) (G := G) (V := V) (W := W) (U := U) := by
  intro _
  exact ⟨isSmooth_smoothContragredient, fun _ g ℓ v => smoothDualPairing_action g ℓ v,
    fun _ g ℓ v => smoothDualPairing_invariant g ℓ v,
    fun _ _ f ℓ v => contragredientMap_apply f ℓ v, fun _ => contragredientMap_id,
    fun _ _ _ f g => contragredientMap_comp f g,
    fun _ hρ v ℓ => smoothBidual_apply hρ v ℓ,
    fun _ _ hρ hσ f => smoothBidual_natural hρ hσ f⟩

end Langlands
