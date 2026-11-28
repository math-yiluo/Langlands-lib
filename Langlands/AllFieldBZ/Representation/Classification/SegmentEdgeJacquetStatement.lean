import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic
import Langlands.Representation.Classification.Segments
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Group.GL.AdjacentMergeShape

/-! The Jacquet filtration after adjacent block replacement. -/

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear Langlands.Geometric Langlands.CuspidalSupport

universe uF uV uW

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- Uniform Jacquet filtration of a product with one merged adjacent slot.
Write `β = uniform m r`, `γ = β.adjacentMerge k`, and `S = β.adjacentRefinement k`,
the refinement of `γ` which splits its merged block back into blocks `k`, `k + 1`.
Assume that every factor `Y_j` of `γ` has zero normalized Jacquet module along
every block shape with at least two blocks other than `S_j`, and that its
normalized Jacquet module along `S_j` is equivalent to the external tensor of
the factors `σ_i` of the original blocks inside block `j`. Then the normalized
`β` Jacquet module of `i_γ(Y)` has a finite filtration with one successive
quotient for each minimal permutation `v` conjugating the Levi of `β` to itself
which is also minimal for `(γ, β)`, equivalent to the Weyl transport by `v` of
`σ_0 ⊗ ⋯ ⊗ σ_(m-1)`. -/
def SegmentEdgeJacquetFiltration : Prop :=
  letI := T.topology
  ∀ (m r : ℕ) (hr : 0 < r) (k : ℕ) (hk : k + 1 < (BlockShape.uniform m r hr).length)
    (σ : ∀ i : Fin (BlockShape.uniform m r hr).length,
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform m r hr).size i) F.Carrier))
    (Y : ∀ j : Fin ((BlockShape.uniform m r hr).adjacentMerge k hk).length,
      SmoothRep.{0, uF, uW} ℂ
        (GeneralLinear (((BlockShape.uniform m r hr).adjacentMerge k hk).size j) F.Carrier)),
    (∀ j (D : BlockShape (((BlockShape.uniform m r hr).adjacentMerge k hk).size j)),
      1 < D.length → D ≠ (BlockShape.uniform m r hr).adjacentRefinement k hk j →
        Subsingleton ((T.normalizedJacquetFunctor D).obj (Y j))) →
    (∀ j, Nonempty (((T.normalizedJacquetFunctor
        ((BlockShape.uniform m r hr).adjacentRefinement k hk j)).obj (Y j)).representation.Equiv
      (FiniteTensor.externalSmoothObject (fun t =>
        σ ((BlockShape.uniform m r hr).adjacentBlockEquiv k hk ⟨j, t⟩))).representation)) →
    ∃ (N : ℕ) (e : Fin N ≃ {v : MinimalConjugatingPermutations (F := F.Carrier)
          (BlockShape.uniform m r hr) (BlockShape.uniform m r hr) //
        IsMinimalRepresentative ((BlockShape.uniform m r hr).adjacentMerge k hk)
          (BlockShape.uniform m r hr) v.val.val})
      (s : ObjectRepFiltration (Rep.of ((T.normalizedJacquetFunctor
          (BlockShape.uniform m r hr)).obj ((T.normalizedProductInductionFunctor
            ((BlockShape.uniform m r hr).adjacentMerge k hk)).obj Y)).representation) N),
      ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
        (transport (BlockShape.uniform m r hr) (BlockShape.uniform m r hr)
          (e i).val.val.val (e i).val.property
          (FiniteTensor.externalSmoothObject σ).representation))

end Langlands.AllFieldBZ.Classification
