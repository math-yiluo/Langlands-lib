import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Category.FiniteIndexRestriction
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteLength

/-! Actual embeddings of a strong socle into nonzero Artinian subobjects. -/

noncomputable section

namespace Langlands.Classification

universe uG uV

variable {G : Type uG} [Group G]
  {V W U : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  {ρ : Representation ℂ G V} {π : Representation ℂ G W}
  {σ : Representation ℂ G U}

/-- The supplied strong socle embeds in every nonzero Artinian representation
that embeds in the ambient representation. -/
def IsIrreducibleSocle.artinianSubobjectEmbedding
    (h : IsIrreducibleSocle ρ π) [Nontrivial U]
    (hσ : IsArtinian (MonoidAlgebra ℂ G) σ.asModule)
    (i : σ.IntertwiningMap ρ) (hi : Function.Injective i) :
    {j : π.IntertwiningMap σ // Function.Injective j} :=
  Classical.choice (by
    let := hσ
    let : Nontrivial σ.asModule := by
      change Nontrivial U
      infer_instance
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)
    obtain ⟨N, hN⟩ := IsAtomic.exists_atom
      (α := Submodule (MonoidAlgebra ℂ G) σ.asModule)
    let S := e.symm N
    have hS : IsAtom S := (e.symm.isAtom_iff N).mpr hN
    have hSir := FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS
    let jS : S.toRepresentation.IntertwiningMap σ :=
      { toLinearMap := S.toSubmodule.subtype
        isIntertwining' := fun _ => by ext x; rfl }
    have hjS : Function.Injective jS := Subtype.val_injective
    let jρ := i.comp jS
    have hjρ : Function.Injective jρ := hi.comp hjS
    let eS := socleEquivOfInjective jρ hjρ (h.socle_eq _ hSir jρ hjρ)
    obtain ⟨eπ⟩ := h.nonempty_socleEquiv
    let j := jS.comp (eπ.trans eS.symm).toIntertwiningMap
    exact ⟨⟨j, hjS.comp (eπ.trans eS.symm).injective⟩⟩)

/-- Finite group-algebra length supplies the Artinian premise for the actual
strong-socle embedding. -/
def IsIrreducibleSocle.finiteLengthSubobjectEmbedding
    (h : IsIrreducibleSocle ρ π) [Nontrivial U]
    (hσ : IsFiniteLength (MonoidAlgebra ℂ G) σ.asModule)
    (i : σ.IntertwiningMap ρ) (hi : Function.Injective i) :
    {j : π.IntertwiningMap σ // Function.Injective j} :=
  h.artinianSubobjectEmbedding
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hσ).2 i hi

end Langlands.Classification
