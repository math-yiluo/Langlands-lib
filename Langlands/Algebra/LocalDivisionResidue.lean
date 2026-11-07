import Langlands.Algebra.DivisionAlgebraNorm
import Langlands.Algebra.LocalDivisionValuation
import Langlands.Algebra.DivisionValuationResidue
import Mathlib.RingTheory.LittleWedderburn

/-! Compact integers and finite commutative residue of a local central division algebra. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K

/-- The normalized regular norm, using the norm constructed from the given local valuation. -/
@[instance_reducible]
def localDivisionNormedRing : NormedRing D := regularNormedRing K D

/-- The constructed division-algebra norm is compatible with the original scalar action. -/
@[instance_reducible]
def localDivisionNormedAlgebra :
    letI := localDivisionNormedRing K D
    NormedAlgebra K D := regularNormedAlgebra K D

/-- The norm unit ball is precisely the integer set of the canonical local valuation. -/
theorem localDivisionNorm_le_one_iff (x : D) :
    letI := localDivisionNormedRing K D
    ‖x‖ ≤ 1 ↔ localReducedNormValuation K D x ≤ 1 := by
  let := localDivisionNormedRing K D
  change regularAbsoluteValue K D x ≤ 1 ↔ _
  rw [← map_one (regularAbsoluteValue K D), regularAbsoluteValue_le_iff]
  simp only [map_one, norm_one]
  rw [← norm_one (α := K), LocalGalois.localNormedField_le K]
  rw [map_one, valuation_regularNorm_eq_localReducedNormValuation_pow]
  exact pow_le_one_iff_of_nonneg zero_le (CentralSimple.reducedDegree_pos K D).ne'

/-- Strict norm less than one is precisely strict local value less than one. -/
theorem localDivisionNorm_lt_one_iff (x : D) :
    letI := localDivisionNormedRing K D
    ‖x‖ < 1 ↔ localReducedNormValuation K D x < 1 := by
  let := localDivisionNormedRing K D
  change regularAbsoluteValue K D x < 1 ↔ _
  rw [← map_one (regularAbsoluteValue K D), regularAbsoluteValue_lt_iff]
  simp only [map_one, norm_one]
  have h : ‖Algebra.norm K x‖ < ‖(1 : K)‖ ↔
      valuation K (Algebra.norm K x) < valuation K 1 := by
    rw [← not_le, LocalGalois.localNormedField_le K, not_le]
  rw [← norm_one (α := K), h, map_one,
    valuation_regularNorm_eq_localReducedNormValuation_pow]
  exact pow_lt_one_iff_of_nonneg zero_le (CentralSimple.reducedDegree_pos K D).ne'

/-- The actual integer subring is the closed unit ball in the constructed norm. -/
theorem localDivisionInteger_eq_closedBall :
    letI := localDivisionNormedRing K D
    ((localReducedNormValuation K D).integer : Set D) = Metric.closedBall (0 : D) 1 := by
  let := localDivisionNormedRing K D
  ext x
  change localReducedNormValuation K D x ≤ 1 ↔ dist x 0 ≤ 1
  rw [dist_zero_right]
  exact (localDivisionNorm_le_one_iff K D x).symm

/-- The actual integer set is compact in the compatible finite-dimensional topology. -/
theorem localDivisionInteger_isCompact :
    letI := localDivisionNormedRing K D
    IsCompact ((localReducedNormValuation K D).integer : Set D) := by
  let := localDivisionNormedRing K D
  let := localDivisionNormedAlgebra K D
  let : ProperSpace D := FiniteDimensional.proper K D
  rw [localDivisionInteger_eq_closedBall]
  exact isCompact_closedBall _ _

/-- The actual residue division ring of the canonical local valuation is finite. -/
instance localDivisionResidue_finite :
    Finite (DivisionValuation.Residue (localReducedNormValuation K D)) := by
  let := localDivisionNormedRing K D
  obtain ⟨t, ht, hfin, hcover⟩ :=
    (localDivisionInteger_isCompact K D).finite_cover_balls (by norm_num : (0 : ℝ) < 1)
  let center : t → (localReducedNormValuation K D).integer :=
    fun c => ⟨c.val, ht c.property⟩
  let : Finite t := hfin.to_subtype
  apply Finite.of_surjective
    (fun c : t => DivisionValuation.reduction (localReducedNormValuation K D) (center c))
  intro z
  obtain ⟨x, rfl⟩ := DivisionValuation.reduction_surjective (localReducedNormValuation K D) z
  have hx := hcover x.property
  simp only [Set.mem_iUnion] at hx
  obtain ⟨c, hc, hxc⟩ := hx
  refine ⟨⟨c, hc⟩, ?_⟩
  apply (DivisionValuation.reduction_eq_iff _ _ _).mpr
  apply (localDivisionNorm_lt_one_iff K D _).mp
  change ‖c - (x : D)‖ < 1
  rw [← dist_eq_norm, dist_comm]
  exact hxc

/-- Wedderburn makes the actual finite residue division ring a field. -/
@[instance_reducible]
def localDivisionResidueField :
    Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  littleWedderburn _

/-- Commutativity refers to the multiplication already present on the actual residue quotient. -/
theorem localDivisionResidue_mul_comm
    (x y : DivisionValuation.Residue (localReducedNormValuation K D)) : x * y = y * x := by
  let := localDivisionResidueField K D
  exact mul_comm x y

end Langlands.CentralDivision
