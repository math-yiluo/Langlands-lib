import Langlands.Representation.Smooth.IrreducibleGrothendieckProof

/-! Matching actual composition factors give the same exact finite-length class. -/

noncomputable section

open scoped BigOperators

universe uR uG uV

namespace Langlands.SmoothRep.FiniteLengthGrothendieckGroup

open IrreducibleGrothendieckProof VirtualRepresentation

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  {A B : SmoothRep.{uR, uG, uV} k G}

/-- Equality of actual composition factors, with multiplicities, identifies
classes in the full exact quotient, for any finite-length witnesses. -/
theorem ofRepresentation_eq_of_haveSameJordanHolderFactors
    (hA : A.HasFiniteLength) (hB : B.HasFiniteLength)
    (h : HaveSameJordanHolderFactors A.obj B.obj) :
    ofRepresentation A hA = ofRepresentation B hB := by
  obtain ⟨n, s, t, hs, ht, e, he⟩ := h
  have hseries : seriesClass s hs = seriesClass t ht := by
    unfold seriesClass
    calc
      (∑ i, generator (irreducibleIsoClass (gradedSmooth s i) (hs i))) =
          ∑ i, generator (irreducibleIsoClass (gradedSmooth t (e i)) (ht (e i))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg generator
          (irreducibleIsoClass_eq_of_equiv (hs i) (ht (e i)) (he i).some)
      _ = ∑ j, generator (irreducibleIsoClass (gradedSmooth t j) (ht j)) :=
        Equiv.sum_comp e (fun j => generator (irreducibleIsoClass (gradedSmooth t j) (ht j)))
  exact (realize_seriesClass s hs hA).symm.trans
    ((congrArg (realizeIrreducibles k G) hseries).trans (realize_seriesClass t ht hB))

end Langlands.SmoothRep.FiniteLengthGrothendieckGroup
