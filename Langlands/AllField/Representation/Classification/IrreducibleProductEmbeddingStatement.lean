import Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement
import Langlands.AllField.Representation.Induction.BlockFactors
/-! The blockwise supercuspidal embedding statement for normalized products. -/

namespace Langlands.AllField.Classification
open Langlands.Classification hiding IrreducibleProductEmbeddingTheorem
open Langlands.AllField.Classification

open Langlands.GeneralLinear
open Langlands.Geometric

universe uF uV

variable (F : Type uF) [Field F]
  (T : LocalFieldData F)

/-- Every normalized product of irreducible smooth GL factors embeds in the
normalized product of suitable blockwise supercuspidal inductions. This is the
embedding step before flattening and the finite-length argument. -/
def IrreducibleProductEmbeddingTheorem : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F)),
    (∀ i, (A i).IsIrreducible) →
    ∃ (S : BlockRefinement B)
      (C : ∀ i, ∀ j, SupercuspidalRep.{uF, uV}
        (F := F) (n := (S i).size j)),
      ∃ J : ((T.normalizedProductInductionFunctor B).obj A).representation.IntertwiningMap
        ((T.normalizedProductInductionFunctor B).obj
          (fun i => (T.normalizedProductInductionFunctor (S i)).obj
            (fun j => (C i j).obj))).representation,
        Function.Injective J

end Langlands.AllField.Classification
