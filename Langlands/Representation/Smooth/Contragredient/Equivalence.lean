import Langlands.Representation.Smooth.Contragredient.Definitions

/-! # Transport of smooth contragredients along representation equivalences -/

noncomputable section
namespace Langlands

variable {R G V W : Type*} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- An equivalence of representations induces the reverse equivalence of smooth
contragredients. -/
def smoothContragredientEquiv (e : ρ.Equiv σ) :
    (smoothContragredient σ).Equiv (smoothContragredient ρ) :=
  (contragredientMap e.toIntertwiningMap).ofBijective
    ⟨fun ℓ ℓ' h => by
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
      exact congrArg (fun m : SmoothDual ρ => m.val v) h,
    fun ℓ => ⟨contragredientMap e.symm.toIntertwiningMap ℓ, by
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      exact congrArg ℓ.val (e.symm_apply_apply v)⟩⟩


end Langlands
