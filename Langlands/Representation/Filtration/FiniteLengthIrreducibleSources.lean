import Langlands.Representation.Filtration.IrreducibleEmbedding
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Langlands.Representation.Category.Subquotients
import Mathlib.Data.Fintype.EquivFin

/-! Finite representatives for irreducible sources of nonzero intertwiners,
with independent ambient and source carrier universes. -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uK uG uV uW

namespace ObjectRepFiltration

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {A : Rep.{uV} k G} {B : Rep.{uW} k G} {n : ℕ}

/-- A nonzero intertwiner from an irreducible representation to an object with
a supplied composition series identifies its source with a graded quotient. -/
theorem exists_equiv_graded_of_nonzero
    (s : ObjectRepFiltration A n) (hs : s.HasSimpleFactors)
    (hB : B.ρ.IsIrreducible) (f : B.ρ.IntertwiningMap A.ρ) (hf : f ≠ 0) :
    ∃ i : Fin n, Nonempty (B.ρ.Equiv (s.gradedRepresentation i).ρ) := by
  let := hB
  obtain ⟨i, h, hi⟩ := s.exists_mapToGraded_ne_zero f hf
  let := hs i
  exact ⟨i, ⟨(s.mapToGraded f i h).ofBijective
    ⟨(Representation.IsIrreducible.injective_or_eq_zero _).resolve_right hi,
      (Representation.IsIrreducible.surjective_or_eq_zero _).resolve_right hi⟩⟩⟩

end ObjectRepFiltration

namespace SmoothRep

/-- In any chosen source carrier universe, only finitely many irreducible
smooth objects admit a nonzero intertwiner into a fixed finite-length object.
The representatives lie in the source universe; the ambient universe is independent. -/
def FiniteLengthIrreducibleSourcesStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    (A : SmoothRep.{uK, uG, uV} k G),
    A.HasFiniteLength →
    ∃ (n : ℕ) (B : Fin n → SmoothRep.{uK, uG, uW} k G),
      (∀ i, (B i).IsIrreducible) ∧
      ∀ X : SmoothRep.{uK, uG, uW} k G, X.IsIrreducible →
        ∀ f : X.representation.IntertwiningMap A.representation, f ≠ 0 →
          ∃ i, Nonempty (X ≅ B i)

/-- Choose a representative only for those finitely many actual graded factors
that have an irreducible representative in the prescribed source universe. -/
theorem finiteLengthIrreducibleSources :
    FiniteLengthIrreducibleSourcesStatement.{uK, uG, uV, uW} := by
  classical
  intro k _ G _ _ A hA
  obtain ⟨r, s, hs⟩ := MultiplicityAdditivityProof.exists_series hA
  let J := {i : Fin r // ∃ B : SmoothRep.{uK, uG, uW} k G,
    B.IsIrreducible ∧ Nonempty (B.representation.Equiv (s.gradedRepresentation i).ρ)}
  choose B hB he using fun j : J => j.property
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  refine ⟨Fintype.card J, fun i => B (e.symm i), fun i => hB (e.symm i), ?_⟩
  intro X hX f hf
  obtain ⟨i, ⟨g⟩⟩ := s.exists_equiv_graded_of_nonzero hs hX f hf
  let j : J := ⟨i, X, hX, ⟨g⟩⟩
  refine ⟨e j, ?_⟩
  change Nonempty (X ≅ B (e.symm (e j)))
  rw [e.symm_apply_apply]
  obtain ⟨h⟩ := he j
  exact ⟨mkIso (g.trans h.symm)⟩

end SmoothRep

end Langlands
