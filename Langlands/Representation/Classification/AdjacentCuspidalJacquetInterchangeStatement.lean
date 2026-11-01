import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Tensor.Finite

/-!
# Adjacent cuspidal Jacquet interchange under an irreducible commuting pair

An actual supercuspidal block tensor occurring as a subquotient of the normalized
Jacquet module of an irreducible admissible representation along a block shape
also occurs, with two adjacent factors interchanged, along the permuted shape,
provided those two factors form an irreducible commuting binary product.
-/

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- If an actual supercuspidal block tensor is a subquotient of the normalized
Jacquet module of an irreducible admissible finite-length `π`, and the factors at
the adjacent positions `j, j + 1` have an irreducible binary product equivalent to
the rank-cast product in the swapped order, then the tensor with those two factors
interchanged is a subquotient of the Jacquet module along the permuted shape. -/
def AdjacentCuspidalJacquetInterchange : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    ∀ A : ∀ i, SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
        ((T.normalizedJacquetFunctor B).obj π) →
      ∀ (j : ℕ) (hj : j + 1 < B.length),
        let a : Fin B.length := ⟨j, by omega⟩
        let b : Fin B.length := ⟨j + 1, hj⟩
        ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
          ((A a).obj, (A b).obj)).IsIrreducible →
        Nonempty ((T.binaryNormalizedProductFunctor (B.size a) (B.size b)).obj
            ((A a).obj, (A b).obj) ≅
          (Derivative.generalLinearRankCast T (Nat.add_comm (B.size b) (B.size a))).obj
            ((T.binaryNormalizedProductFunctor (B.size b) (B.size a)).obj
              ((A b).obj, (A a).obj))) →
        let σ := B.adjacentSwap j hj
        SmoothRep.IsSubquotient
          (FiniteTensor.externalSmoothObject (fun i => (A (σ i)).obj))
          ((T.normalizedJacquetFunctor (B.permute σ)).obj π)

end Langlands.Classification
