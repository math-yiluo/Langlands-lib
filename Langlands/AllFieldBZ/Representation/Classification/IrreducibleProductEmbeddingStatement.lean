import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement

/-!
# All-field port of `Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Classification
open Langlands.Classification hiding IrreducibleProductEmbeddingTheorem
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
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

end Langlands.AllFieldBZ.Classification
