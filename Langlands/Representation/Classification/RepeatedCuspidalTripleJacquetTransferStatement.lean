import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Tensor.Finite
import Langlands.Group.GL.AdjacentMergeShape

/-!
# Repeated-factor cuspidal triple Jacquet transfers

The two local moves in Jantzen (2000), Lemma 2.2.2, printed pp.545–547,
expressed with actual subquotients and arbitrary unchanged outside factors.
This is a proposition definition, not a proof of either transfer.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- For `A = ν B`, the local moves `(A,B,B) → (B,A,B)` and
`(A,B,A) → (A,A,B) or (B,A,A)` in an actual normalized upper Jacquet module.
Rank-indexed class equalities include the required rank transport. -/
def RepeatedCuspidalTripleJacquetTransfer : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (C : ∀ i : Fin B.length,
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i)),
    π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
    SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
      ((T.normalizedJacquetFunctor B).obj π) →
    ∀ (j : ℕ) (hj : j + 2 < B.length),
      let a : Fin B.length := ⟨j, by omega⟩
      let b : Fin B.length := ⟨j + 1, by omega⟩
      let c : Fin B.length := ⟨j + 2, hj⟩
      let σab := B.adjacentSwap j (by omega)
      let σbc := B.adjacentSwap (j + 1) (by omega)
      (((⟨B.size a, (C a).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
            ⟨B.size b, T.supercuspidalClassRealPowerTwist (B.size b) 1 (C b).isoClass⟩) →
        (⟨B.size c, (C c).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
            ⟨B.size b, (C b).isoClass⟩ →
        SmoothRep.IsSubquotient
          (FiniteTensor.externalSmoothObject (fun i => (C (σab i)).obj))
          ((T.normalizedJacquetFunctor (B.permute σab)).obj π)) ∧
      (((⟨B.size a, (C a).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
            ⟨B.size b, T.supercuspidalClassRealPowerTwist (B.size b) 1 (C b).isoClass⟩) →
        (⟨B.size c, (C c).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)) =
            ⟨B.size a, (C a).isoClass⟩ →
        SmoothRep.IsSubquotient
          (FiniteTensor.externalSmoothObject (fun i => (C (σbc i)).obj))
          ((T.normalizedJacquetFunctor (B.permute σbc)).obj π) ∨
        SmoothRep.IsSubquotient
          (FiniteTensor.externalSmoothObject (fun i => (C (σab i)).obj))
          ((T.normalizedJacquetFunctor (B.permute σab)).obj π))

end Langlands.Classification
