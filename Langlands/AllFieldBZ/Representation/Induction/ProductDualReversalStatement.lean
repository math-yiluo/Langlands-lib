import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Group.GL.ReverseBlocks
import Langlands.Representation.Smooth.Contragredient.Definitions

/-! Inverse transpose and smooth duality for normalized ordered products. -/

namespace Langlands.AllFieldBZ.Parabolic

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData

universe uF uV

/-- Pulling the normalized product of irreducible smooth factors back along
inverse transpose gives the smooth dual of the reversed normalized product. -/
def ProductDualReversalStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
      (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, (A i).IsIrreducible) →
    letI := T.generalLinearTopologicalGroup n
    let I := (T.normalizedProductInductionFunctor B).obj A
    let J := (T.normalizedProductInductionFunctor B.reverse).obj (fun i => A i.rev)
    Nonempty (Representation.Equiv
      (I.representation.comp (inverseTranspose n F.Carrier).toMonoidHom)
      (smoothContragredient J.representation))

end Langlands.AllFieldBZ.Parabolic
