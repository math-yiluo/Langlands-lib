import Langlands.Representation.Classification.StrongConstituentExtremaStatement
import Langlands.Representation.Classification.Cosocle
import Langlands.Representation.Category.FiniteIndexRestriction

/-!
# Strong irreducible constituents from unique atoms and coatoms

The proof uses actual quotient maps and subrepresentation inclusions. It
preserves equality of their kernels and images.
-/

noncomputable section

namespace Langlands.Classification

open scoped MonoidAlgebra

universe uG uV

variable {G : Type uG} [Group G] {V : Type uV}
  [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

private theorem isAtom_range_of_irreducible_injective
    {W : Type uV} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G W} (hπ : Representation.IsIrreducible π)
    (j : π.IntertwiningMap ρ) (hj : Function.Injective j) :
    IsAtom j.range := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let f : π.asModule →ₗ[ℂ[G]] e j.range :=
    (Representation.IntertwiningMap.equivLinearMapAsModule π ρ j).codRestrict
      (e j.range) (fun w => ⟨w, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => hj (congrArg Subtype.val h), ?_⟩
    rintro ⟨v, w, hw⟩
    exact ⟨w, Subtype.ext hw⟩
  apply (e.isAtom_iff j.range).mp
  apply isSimpleModule_iff_isAtom.mp
  exact (f.isSimpleModule_iff_of_bijective hf).mp
    ((Representation.irreducible_iff_isSimpleModule_asModule π).mp hπ)

private theorem strongHead_of_unique_coatom
    (h : ∃! S : Subrepresentation ρ, IsCoatom S) :
    IsIrreducibleHead ρ (head ρ) := by
  obtain ⟨S, hS, huniq⟩ := h
  let π := ρ.quotient S.toSubmodule fun g _ hw => S.apply_mem_toSubmodule g hw
  let q : ρ.IntertwiningMap π :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hker : q.ker = S :=
    Subrepresentation.toSubmodule_injective (Submodule.ker_mkQ S.toSubmodule)
  have hπ := (isIrreducible_iff_isCoatom_ker q hq).mpr (by rw [hker]; exact hS)
  have hh : IsIrreducibleHead ρ π := by
    refine ⟨hπ, q, hq, ?_⟩
    intro W' _ _ π' hπ' q' hq'
    exact congrArg Subrepresentation.toSubmodule
      ((huniq q'.ker ((isIrreducible_iff_isCoatom_ker q' hq').mp hπ')).trans hker.symm)
  exact hh.isIrreducibleHead_head

private theorem unique_coatom_of_strongHead
    (h : IsIrreducibleHead ρ (head ρ)) :
    ∃! S : Subrepresentation ρ, IsCoatom S := by
  obtain ⟨hπ, q, hq, huniq⟩ := h
  refine ⟨q.ker, (isIrreducible_iff_isCoatom_ker q hq).mp hπ, ?_⟩
  intro S hS
  let σ := ρ.quotient S.toSubmodule fun g _ hw => S.apply_mem_toSubmodule g hw
  let qS : ρ.IntertwiningMap σ :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  have hqS : Function.Surjective qS := Submodule.mkQ_surjective _
  have hker : qS.ker = S :=
    Subrepresentation.toSubmodule_injective (Submodule.ker_mkQ S.toSubmodule)
  have hσ := (isIrreducible_iff_isCoatom_ker qS hqS).mpr (by rw [hker]; exact hS)
  apply Subrepresentation.toSubmodule_injective
  exact (congrArg Subrepresentation.toSubmodule hker.symm).trans
    (huniq _ σ hσ qS hqS)

private theorem strongSocle_of_unique_atom
    (h : ∃! S : Subrepresentation ρ, IsAtom S) :
    IsIrreducibleSocle ρ (socleRepresentation ρ) := by
  obtain ⟨S, hS, huniq⟩ := h
  let j : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hj : Function.Injective j := Subtype.val_injective
  have hπ := FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS
  have hrange : j.range = S :=
    Subrepresentation.toSubmodule_injective (Submodule.range_subtype S.toSubmodule)
  have hs : IsIrreducibleSocle ρ S.toRepresentation := by
    refine ⟨hπ, j, hj, ?_⟩
    intro W' _ _ π' hπ' j' hj'
    exact congrArg Subrepresentation.toSubmodule
      ((huniq j'.range (isAtom_range_of_irreducible_injective hπ' j' hj')).trans
        hrange.symm)
  exact hs.isIrreducibleSocle_socleRepresentation

private theorem unique_atom_of_strongSocle
    (h : IsIrreducibleSocle ρ (socleRepresentation ρ)) :
    ∃! S : Subrepresentation ρ, IsAtom S := by
  obtain ⟨hπ, j, hj, huniq⟩ := h
  refine ⟨j.range, isAtom_range_of_irreducible_injective hπ j hj, ?_⟩
  intro S hS
  let jS : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hjS : Function.Injective jS := Subtype.val_injective
  have hσ := FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS
  have hrange : jS.range = S :=
    Subrepresentation.toSubmodule_injective (Submodule.range_subtype S.toSubmodule)
  apply Subrepresentation.toSubmodule_injective
  exact (congrArg Subrepresentation.toSubmodule hrange.symm).trans
    (huniq _ S.toRepresentation hσ jS hjS)

/-- Unique lattice extrema give exactly the canonical strong constituents. -/
theorem strongConstituentExtrema : StrongConstituentExtremaStatement.{uG, uV} := by
  intro G _ V _ _ ρ
  exact ⟨⟨strongHead_of_unique_coatom, unique_coatom_of_strongHead⟩,
    ⟨strongSocle_of_unique_atom, unique_atom_of_strongSocle⟩⟩

end Langlands.Classification
