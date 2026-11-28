import Langlands.Representation.FiniteGeneralLinear.FiniteProductIrreducibles
import Langlands.Representation.FiniteVectors

/-! # An irreducible external tensor constituent through a nonzero vector

A representation of a finite product of finite groups on an arbitrary complex vector space
with a nonzero vector contains, as a subrepresentation, an external tensor product of chosen
irreducible representatives of the factors.
-/

noncomputable section

open Module Representation

namespace Langlands.FiniteRep

universe uG uX

variable {ι : Type} [Fintype ι] {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, Finite (G i)]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- **An external tensor constituent.** Let `σ` be a complex representation of a finite
product `∏_i G_i` of finite groups on a vector space `X`, and let `v ∈ X` be nonzero. There are
irreducible classes `a_i` of the factors and an injective linear map from the external tensor
product of the chosen representatives of the `a_i` to `X` intertwining it with `σ`. -/
theorem exists_externalRep_intertwining (σ : Representation ℂ (∀ i, G i) X) {v : X}
    (hv : v ≠ 0) :
    ∃ (a : ∀ i, IrreducibleClass (G i))
      (f : (externalRep fun i => VirtualCharacter.rep (a i)) →ₗ[ℂ] X),
      Function.Injective f ∧
        ∀ (g : ∀ i, G i) (x : externalRep fun i => VirtualCharacter.rep (a i)),
          f ((externalRep fun i => VirtualCharacter.rep (a i)).ρ g x) = σ g (f x) := by
  classical
  let : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
  let S := FiniteVectors.orbitSubrepresentation σ v
  have hfin : Module.Finite ℂ S.toSubmodule :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let v₀ : S.toSubmodule := ⟨v, FiniteVectors.self_mem_orbitSpan σ v⟩
  have hv₀ : v₀ ≠ 0 := fun h => hv (congrArg Subtype.val h)
  let m := finrank ℂ S.toSubmodule
  let e : S.toSubmodule ≃ₗ[ℂ] (Fin m → ℂ) := (Module.finBasis ℂ S.toSubmodule).equivFun
  let τ : Representation ℂ (∀ i, G i) (Fin m → ℂ) :=
    (MonoidHom.ofClass (e.conjAlgEquiv ℂ)).comp S.toRepresentation
  have hm : finrank ℂ (Fin m → ℂ) ≠ 0 := by
    rw [Module.finrank_fin_fun]
    exact (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v₀, hv₀⟩).ne'
  obtain ⟨T, hT⟩ := FiniteCharacter.exists_isAtom τ hm
  let A : FDRep ℂ (∀ i, G i) := FDRep.of T.toRepresentation
  have hA : IsIrreducible A.ρ :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom T hT
  obtain ⟨a, ⟨E⟩⟩ := exists_externalRep_equiv A hA
  let f : (externalRep fun i => VirtualCharacter.rep (a i)) →ₗ[ℂ] X :=
    S.toSubmodule.subtype ∘ₗ e.symm.toLinearMap ∘ₗ T.toSubmodule.subtype ∘ₗ
      E.symm.toLinearEquiv.toLinearMap
  refine ⟨a, f, ?_, ?_⟩
  · exact Subtype.val_injective.comp (e.symm.injective.comp
      (Subtype.val_injective.comp E.symm.toLinearEquiv.injective))
  · intro g x
    have hE := IntertwiningMap.isIntertwining _ _ E.symm.toIntertwiningMap g x
    change ((e.symm (T.toSubmodule.subtype (E.symm.toLinearEquiv
      ((externalRep fun i => VirtualCharacter.rep (a i)).ρ g x)))) : X) = _
    rw [show E.symm.toLinearEquiv ((externalRep fun i => VirtualCharacter.rep (a i)).ρ g x) =
      A.ρ g (E.symm.toLinearEquiv x) from hE]
    change ((e.symm (e (S.toRepresentation g
      (e.symm ((E.symm.toLinearEquiv x : T.toSubmodule) : Fin m → ℂ))))) : X) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

end Langlands.FiniteRep
