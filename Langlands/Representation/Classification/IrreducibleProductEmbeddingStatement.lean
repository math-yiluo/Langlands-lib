import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Geometric.WeylDefinitions

/-! The blockwise supercuspidal embedding statement for normalized products. -/

namespace Langlands.Classification

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Every normalized product of irreducible smooth GL factors embeds in the
normalized product of suitable blockwise supercuspidal inductions. This is the
embedding step before flattening and the finite-length argument. -/
def IrreducibleProductEmbeddingTheorem : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, (A i).IsIrreducible) →
    ∃ (S : BlockRefinement B)
      (C : ∀ i, ∀ j, SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := (S i).size j)),
      ∃ J : ((T.normalizedProductInductionFunctor B).obj A).representation.IntertwiningMap
        ((T.normalizedProductInductionFunctor B).obj
          (fun i => (T.normalizedProductInductionFunctor (S i)).obj
            (fun j => (C i j).obj))).representation,
        Function.Injective J

end Langlands.Classification
