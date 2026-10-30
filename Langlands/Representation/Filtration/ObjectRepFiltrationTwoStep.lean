import Langlands.Representation.Filtration.FunctorLengthTwoDetection

namespace Langlands.LengthTwo

universe uK uG uV

open Representation
open LengthCriterionProof (quotientRep)

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The actual two-step filtration, with its simple factors and their
identifications, from an irreducible subspace and irreducible quotient. -/
noncomputable def irreducibleTwoStep (K : Subrepresentation ρ)
    (hK : IsIrreducible K.toRepresentation)
    (hQ : IsIrreducible (quotientRep K ⊤)) :
    {s : ObjectRepFiltration (Rep.of ρ) 2 //
      s.HasSimpleFactors ∧ s.subrepresentation 1 = K ∧
      Nonempty ((s.gradedRepresentation 0).ρ.Equiv K.toRepresentation) ∧
      Nonempty ((s.gradedRepresentation 1).ρ.Equiv (quotientRep K ⊤))} := by
  refine ⟨twoStep K, ?_⟩
  obtain ⟨e⟩ := FunctorLengthTwo.nonempty_quotientBot_equiv K
  refine ⟨?_, rfl, ⟨e⟩, ⟨Representation.Equiv.refl _⟩⟩
  intro i
  fin_cases i
  · exact isIrreducible_of_equiv e.symm hK
  · exact hQ

@[simp]
theorem irreducibleTwoStep_filtration (K : Subrepresentation ρ)
    (hK : IsIrreducible K.toRepresentation)
    (hQ : IsIrreducible (quotientRep K ⊤)) :
    (irreducibleTwoStep K hK hQ).val = twoStep K := rfl

/-- The standard two-step filtration has the supplied irreducible subspace and
quotient as its actual simple factors. -/
theorem exists_twoStep_of_irreducible (K : Subrepresentation ρ)
    (hK : IsIrreducible K.toRepresentation)
    (hQ : IsIrreducible (quotientRep K ⊤)) :
    ∃ s : ObjectRepFiltration (Rep.of ρ) 2,
      s.HasSimpleFactors ∧ s.subrepresentation 1 = K ∧
      Nonempty ((s.gradedRepresentation 0).ρ.Equiv K.toRepresentation) ∧
      Nonempty ((s.gradedRepresentation 1).ρ.Equiv (quotientRep K ⊤)) :=
  ⟨(irreducibleTwoStep K hK hQ).val, (irreducibleTwoStep K hK hQ).property⟩

end Langlands.LengthTwo
