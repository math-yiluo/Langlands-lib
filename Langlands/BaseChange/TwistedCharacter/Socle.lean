import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Classification.Cosocle
import Langlands.Representation.CompactCoefficient.IsotypicSemisimplicityProof
import Langlands.Representation.CuspidalSupport.NormalRestrictionCovariance
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Finite.CharacterTheoryProof

/-! # The socle of a representation with a twisting isomorphism -/

noncomputable section

namespace Langlands.BaseChange

open Classification

universe uG z

variable {G : Type uG} [Group G] {V : Type z} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

private theorem isAtom_range_of_injective {W : Type z} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G W} (hirr : π.IsIrreducible) (j : π.IntertwiningMap ρ)
    (hj : Function.Injective j) : IsAtom j.range :=
  NormalRestrictionOrbit.isAtom_of_isIrreducible _
    ((isIrreducible_iff_of_equiv (FiniteCharacter.equivRange j hj)).mp hirr)

/-- The Library socle is the sum of the minimal nonzero invariant subspaces. -/
theorem socle_eq_iSup_atoms (ρ : Representation ℂ G V) :
    socle ρ = ⨆ S : {S : Subrepresentation ρ // IsAtom S}, S.val := by
  classical
  apply Subrepresentation.toSubmodule_injective
  rw [Langlands.Subrepresentation.toSubmodule_iSup]
  change sSup (irreducibleImages ρ) = _
  refine le_antisymm (sSup_le ?_) (iSup_le ?_)
  · rintro _ ⟨W, hW, hM, π, j, hπ, hj, rfl⟩
    let := hW
    let := hM
    exact le_iSup (fun S : {S : Subrepresentation ρ // IsAtom S} => S.val.toSubmodule)
      ⟨j.range, isAtom_range_of_injective hπ j hj⟩
  · intro ⟨S, hS⟩
    let j : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have h := range_le_socle S.toRepresentation
      (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS) j Subtype.val_injective
    exact (Submodule.range_subtype S.toSubmodule).symm.le.trans h

/-- The canonical socle is semisimple as a module over the group algebra. -/
theorem isSemisimpleModule_socle (ρ : Representation ℂ G V) :
    IsSemisimpleModule (MonoidAlgebra ℂ G) (socleRepresentation ρ).asModule := by
  apply (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
  change Representation.IsSemisimpleRepresentation (socle ρ).toRepresentation
  rw [socle_eq_iSup_atoms]
  exact CompactCoefficientClass.isSemisimpleRepresentation_iSup _
    (fun S => isSemisimpleRepresentation_of_isIrreducible
      (FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom _ S.property))

/-- A nonzero Artinian representation has nonzero socle. -/
theorem socle_ne_bot_of_artinian [Nontrivial V]
    [IsArtinian (MonoidAlgebra ℂ G) ρ.asModule] : socle ρ ≠ ⊥ := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let : Nontrivial ρ.asModule := ‹Nontrivial V›
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (α := Submodule (MonoidAlgebra ℂ G) ρ.asModule)
  have h : IsAtom (e.symm S) := (e.symm.isAtom_iff S).mpr hS
  intro hs
  have hi : e.symm S ≤ socle ρ := by
    rw [socle_eq_iSup_atoms]
    exact le_iSup (fun S : {S : Subrepresentation ρ // IsAtom S} => S.val) ⟨e.symm S, h⟩
  exact h.ne_bot (le_bot_iff.mp (hi.trans hs.le))

/-- The inverse linear map intertwines the representation with its pullback by `θ⁻¹`. -/
def inverseTwistingEquiv (θ : G ≃* G) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    ρ.Equiv (ρ.comp θ.symm.toMonoidHom) :=
  Representation.Equiv.mk A.toLinearEquiv.symm fun g => by
    ext v
    apply A.injective
    change A (A.symm (ρ g v)) = A (ρ (θ.symm g) (A.symm v))
    rw [A.apply_symm_apply]
    have h := LinearMap.congr_fun (A.isIntertwining' (θ.symm g)) (A.symm v)
    change A (ρ (θ.symm g) (A.symm v)) = ρ (θ (θ.symm g)) (A (A.symm v)) at h
    rw [θ.apply_symm_apply, A.apply_symm_apply] at h
    exact h.symm

private theorem map_socle_le (θ : G ≃* G) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    (socle ρ).toSubmodule.map A.toLinearMap ≤ (socle ρ).toSubmodule := by
  rw [Submodule.map_le_iff_le_comap]
  change sSup (irreducibleImages ρ) ≤ _
  apply sSup_le
  rintro _ ⟨W, hW, hM, π, j, hπ, hj, rfl⟩ _ ⟨x, rfl⟩
  let := hW
  let := hM
  let i : Representation.IntertwiningMap (π.comp θ.symm.toMonoidHom) ρ :=
    ⟨A.toLinearMap ∘ₗ j.toLinearMap, fun g => by
      ext x
      change A (j (π (θ.symm g) x)) = ρ g (A (j x))
      rw [j.isIntertwining]
      have h := LinearMap.congr_fun (A.isIntertwining' (θ.symm g)) (j x)
      change A (ρ (θ.symm g) (j x)) = ρ (θ (θ.symm g)) (A (j x)) at h
      rwa [θ.apply_symm_apply] at h⟩
  have hirr := (CuspidalSupport.isIrreducible_comp_mulEquiv_iff π θ.symm).mpr hπ
  exact range_le_socle _ hirr i (A.injective.comp hj) ⟨x, rfl⟩

/-- The underlying linear map of a twisting isomorphism maps the canonical socle onto itself. -/
theorem map_socle_eq (θ : G ≃* G) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    (socle ρ).toSubmodule.map A.toLinearMap = (socle ρ).toSubmodule := by
  refine le_antisymm (map_socle_le θ A) ?_
  intro v hv
  exact ⟨A.symm v, map_socle_le θ.symm (inverseTwistingEquiv θ A) ⟨v, hv, rfl⟩,
    A.apply_symm_apply v⟩

end Langlands.BaseChange
