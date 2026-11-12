import Langlands.Representation.CuspidalSupport.BernsteinBlockAbelianProof

/-! # Reducing the aggregate Bernstein target to the decomposition theorem -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- If every smooth object has a Bernstein-block coproduct presentation, every
subrepresentation has one as well. The given presentation of the larger object
is unnecessary for this consequence of the full decomposition theorem. -/
theorem bernsteinSplitSubrepresentation_of_decomposition
    (h : BernsteinDecompositionStatement.{uF, uV}) :
    BernsteinSplitSubrepresentationStatement.{uF, uV} := by
  intro F _ _ _ _ G _ _ T i ν
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ family V S _
  exact (h F G T i ν family).1 (SmoothRep.subrepresentation V S)

/-- The full aggregate target is equivalent to its decomposition conjunct:
subrepresentation splitting follows by applying that conjunct to the
subrepresentation, and the block-abelian conjunct is already proved. -/
theorem bernsteinDecompositionStatements_iff_decomposition :
    BernsteinDecompositionStatements.{uF, uV} ↔
      BernsteinDecompositionStatement.{uF, uV} := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, bernsteinSplitSubrepresentation_of_decomposition h, bernsteinBlockAbelian⟩

/-- The explicit equivalence of proof types underlying the aggregate reduction.
Its inverse assembles the aggregate from a proof of the decomposition conjunct. -/
def bernsteinDecompositionProofEquiv :
    BernsteinDecompositionStatements.{uF, uV} ≃
      BernsteinDecompositionStatement.{uF, uV} :=
  Equiv.ofIff bernsteinDecompositionStatements_iff_decomposition

end Langlands.CuspidalSupport
