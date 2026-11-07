import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedField
import Langlands.Global.CompletionIntegersSmoothPointLifting
import Langlands.Global.Adelic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# The local fields of the adelic level rings

The completions occurring in the adelic level rings are complete nontrivially normed fields
whose norm induces their given topology, and they are henselian valued fields:

* a height-one completion `v.adicCompletion F` of the fraction field of a Dedekind domain,
  normed through its discrete valuation, is non-archimedean, its completed valuation ring is
  its closed unit ball, and that ring is henselian;
* an archimedean completion of a number field embeds isometrically in `ℂ`.
-/

noncomputable section

universe u

open IsDedekindDomain
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)
open Langlands.AlgebraicGeometry.PointTopology.CompleteHenselian

namespace Langlands.Global

namespace AdelicSpaceLocalFields

section Adic

variable (A : Type u) [CommRing A] [IsDedekindDomain A] (F : Type u) [Field F] [Algebra A F]
  [IsFractionRing A F] (v : HeightOneSpectrum A)

/-- The rank-one structure of the completed discrete valuation, with base `2`. -/
@[instance_reducible]
def rankOne : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)

/-- The nontrivially normed field structure of a height-one completion. -/
@[instance_reducible]
def normedField : NontriviallyNormedField (v.adicCompletion F) :=
  let := rankOne A F v
  Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))

/-- The norm induces the given topology. -/
theorem normedField_topology :
    (normedField A F v).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (v.adicCompletion F)) := rfl

/-- The completed valuation ring is the closed unit ball. -/
theorem mem_adicCompletionIntegers_iff (x : v.adicCompletion F) :
    x ∈ (v.adicCompletionIntegers F).toSubring ↔ @Norm.norm _ (normedField A F v).toNorm x ≤ 1 := by
  let := rankOne A F v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers A F v).trans
    Valued.toNormedField.norm_le_one_iff.symm

theorem isUltrametricDist :
    @IsUltrametricDist (v.adicCompletion F) (normedField A F v).toDist := by
  let := rankOne A F v
  let := normedField A F v
  exact ⟨fun x y z => by
    refine (Valuation.norm_add_le _ (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl⟩

theorem completeSpace : @CompleteSpace (v.adicCompletion F) (normedField A F v).toUniformSpace :=
  (inferInstance : CompleteSpace (v.adicCompletion F))

/-- **A height-one completion is a henselian valued field.** -/
theorem isHenselianValuedField : @IsHenselianValuedField (v.adicCompletion F) (normedField A F v) :=
  @isHenselianValuedField_of_isUltrametricDist _ (normedField A F v) (completeSpace A F v)
    (isUltrametricDist A F v)

/-- The completed valuation ring is henselian. -/
theorem henselianLocalRing : HenselianLocalRing (v.adicCompletionIntegers F).toSubring :=
  adicCompletionIntegers_henselian A F v

end Adic

section Infinite

variable (K : Type u) [Field K] (v : InfinitePlace K)

/-- The nontrivially normed field structure of an archimedean completion. -/
@[instance_reducible]
def infiniteNormedField : NontriviallyNormedField (InfiniteCompletion K v) :=
  { (inferInstance : NormedField (InfiniteCompletion K v)) with
    non_trivial := by
      refine ⟨2, ?_⟩
      have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
          (map_zero (NumberField.InfinitePlace.Completion.extensionEmbedding v))
          (2 : InfiniteCompletion K v)
      rw [← h]
      norm_num only [map_ofNat, Complex.norm_ofNat] }

/-- **An archimedean completion is a henselian valued field.** -/
theorem infinite_isHenselianValuedField :
    @IsHenselianValuedField (InfiniteCompletion K v) (infiniteNormedField K v) :=
  @isHenselianValuedField_of_isometry _ (infiniteNormedField K v)
    (inferInstance : CompleteSpace (InfiniteCompletion K v))
    (NumberField.InfinitePlace.Completion.extensionEmbedding v)
    (fun x => (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _) x)

end Infinite

end AdelicSpaceLocalFields

end Langlands.Global
