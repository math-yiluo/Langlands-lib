import Langlands.Representation.Filtration.JordanHolderStatement
import Langlands.Representation.Filtration.LengthCriterionProof
import Mathlib.LinearAlgebra.Isomorphisms

/-! Actual equivariant Jordan–Hölder comparison and transitivity. -/

namespace Langlands

universe uK uG uA uB uC

namespace JordanHolderProof

open LengthCriterionProof

section Intervals

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uA} [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- The invariant subspace lattice inherits modularity from submodules. -/
instance subrepresentationIsModularLattice : IsModularLattice (Subrepresentation ρ) :=
  ⟨fun {x} y {z} hxz => by
    change ((x.toSubmodule ⊔ y.toSubmodule) ⊓ z.toSubmodule : Submodule k V) ≤
      x.toSubmodule ⊔ (y.toSubmodule ⊓ z.toSubmodule)
    exact IsModularLattice.sup_inf_le_assoc_of_le y.toSubmodule hxz⟩

/-- The second isomorphism theorem commutes with the representation action. -/
noncomputable def quotientSecondIso (x y : Subrepresentation ρ) :
    (quotientRep (y ⊓ x) y).Equiv (quotientRep x (y ⊔ x)) :=
  Representation.Equiv.mk (LinearMap.quotientInfEquivSupQuotient y.toSubmodule x.toSubmodule)
    (by
      intro g
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro v
      rfl)

/-- Every lattice interval equivalence gives an actual equivariant quotient isomorphism. -/
theorem quotientEquiv_of_intervalIso
    {X Y : Subrepresentation ρ × Subrepresentation ρ}
    (h : JordanHolderLattice.Iso X Y) :
    Nonempty ((quotientRep X.1 X.2).Equiv (quotientRep Y.1 Y.2)) := by
  let e : (Subrepresentation ρ × Subrepresentation ρ) →
      (Subrepresentation ρ × Subrepresentation ρ) → Prop :=
    fun X Y => Nonempty ((quotientRep X.1 X.2).Equiv (quotientRep Y.1 Y.2))
  exact h.rel e ⟨Representation.Equiv.refl _⟩
    (fun ⟨f⟩ => ⟨f.symm⟩) (fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩)
    (fun {x y} _ => by
      change e (x, x ⊔ y) (x ⊓ y, y)
      rw [sup_comm x y, inf_comm x y]
      exact ⟨(quotientSecondIso x y).symm⟩)

end Intervals

end JordanHolderProof

open JordanHolderProof LengthCriterionProof

set_option maxHeartbeats 800000 in
/-- Two supplied actual composition series match by a multiplicity-preserving bijection. -/
theorem jordanHolderSeriesComparison : JordanHolderSeriesComparisonStatement.{uK, uG, uA} := by
  intro k _ G _ A n m s t hs ht
  let S : CompositionSeries (Subrepresentation A.ρ) :=
    ⟨n, s.subrepresentation, (hasSimpleFactors_iff_covBy s).mp hs⟩
  let T : CompositionSeries (Subrepresentation A.ρ) :=
    ⟨m, t.subrepresentation, (hasSimpleFactors_iff_covBy t).mp ht⟩
  have hhead : S.head = T.head := by
    change s.subrepresentation 0 = t.subrepresentation 0
    simp only [ObjectRepFiltration.subrepresentation_zero]
  have hlast : S.last = T.last := by
    change s.subrepresentation (Fin.last n) = t.subrepresentation (Fin.last m)
    simp only [ObjectRepFiltration.subrepresentation_last]
  obtain ⟨e, he⟩ := CompositionSeries.jordan_holder S T hhead hlast
  exact ⟨e, fun i => quotientEquiv_of_intervalIso (he i)⟩

/-- Compare the two independently chosen middle series before composing factor matches. -/
theorem haveSameJordanHolderFactors_trans :
    HaveSameJordanHolderFactorsTransStatement.{uK, uG, uA, uB, uC} := by
  intro k _ G _ A B C hAB hBC
  obtain ⟨n, sA, sB, hsA, hsB, e, he⟩ := hAB
  obtain ⟨m, tB, tC, htB, htC, f, hf⟩ := hBC
  obtain ⟨g, hg⟩ := jordanHolderSeriesComparison k G B n m sB tB hsB htB
  have hnm : n = m := Fintype.card_fin n ▸ Fintype.card_fin m ▸ Fintype.card_congr g
  subst m
  refine ⟨n, sA, tC, hsA, htC, e.trans (g.trans f), ?_⟩
  intro i
  obtain ⟨p⟩ := he i
  obtain ⟨q⟩ := hg (e i)
  obtain ⟨r⟩ := hf (g (e i))
  exact ⟨(p.trans q).trans r⟩

end Langlands
