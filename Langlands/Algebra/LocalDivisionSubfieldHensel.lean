import Langlands.Algebra.LocalDivisionResidueSubfield
import Mathlib.RingTheory.Henselian

/-! Compatible local-field topology and actual Hensel lifting in an embedded subfield. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  {L : Type uL} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K

/-- Pull back the actual normalized determinant absolute value along the original embedding. -/
def localDivisionSubfieldAbsoluteValue : AbsoluteValue L ℝ where
  toFun x := regularAbsoluteValue K D (ι x)
  map_mul' x y := by rw [map_mul, map_mul]
  nonneg' x := (regularAbsoluteValue K D).nonneg _
  eq_zero' x := by
    rw [(regularAbsoluteValue K D).eq_zero]
    exact map_eq_zero_iff ι ι.injective
  add_le' x y := by
    rw [map_add]
    exact (regularAbsoluteValue K D).add_le _ _

/-- The pulled-back norm preserves the original field operations. -/
@[instance_reducible]
def localDivisionSubfieldNormedField : NormedField L :=
  (localDivisionSubfieldAbsoluteValue K D ι).toNormedField

/-- The pulled-back norm preserves the original scalar action. -/
@[instance_reducible]
def localDivisionSubfieldNormedAlgebra :
    letI := localDivisionSubfieldNormedField K D ι
    NormedAlgebra K L := by
  let := localDivisionSubfieldNormedField K D ι
  refine { ‹Algebra K L› with norm_smul_le := fun c x => ?_ }
  change regularAbsoluteValue K D (ι (c • x)) ≤
    ‖c‖ * regularAbsoluteValue K D (ι x)
  rw [map_smul, Algebra.smul_def, map_mul, regularAbsoluteValue_algebraMap]

/-- The norm order is exactly the order of the restricted original local valuation. -/
theorem localDivisionSubfield_norm_le_iff (x y : L) :
    letI := localDivisionSubfieldNormedField K D ι
    ‖x‖ ≤ ‖y‖ ↔
      localDivisionSubfieldValuation K D ι x ≤ localDivisionSubfieldValuation K D ι y := by
  let := localDivisionSubfieldNormedField K D ι
  change regularAbsoluteValue K D (ι x) ≤ regularAbsoluteValue K D (ι y) ↔ _
  rw [regularAbsoluteValue_le_iff, LocalGalois.localNormedField_le K,
    valuation_regularNorm_eq_localReducedNormValuation_pow,
    valuation_regularNorm_eq_localReducedNormValuation_pow]
  exact pow_le_pow_iff_left₀ zero_le zero_le (CentralSimple.reducedDegree_pos K D).ne'

omit [Algebra.IsCentral K D] in
/-- The pulled-back norm is ultrametric. -/
theorem localDivisionSubfield_ultrametric :
    letI := localDivisionSubfieldNormedField K D ι
    IsUltrametricDist L := by
  let := localDivisionSubfieldNormedField K D ι
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  change regularAbsoluteValue K D (ι (x + y)) ≤
    max (regularAbsoluteValue K D (ι x)) (regularAbsoluteValue K D (ι y))
  rw [map_add]
  exact regularAbsoluteValue_add_le K D _ _

/-- The valuative relation is obtained from restriction of the original division-algebra valuation. -/
@[instance_reducible]
def localDivisionSubfieldValuativeRel : ValuativeRel L :=
  ValuativeRel.ofValuation (localDivisionSubfieldValuation K D ι)

/-- The restricted valuation is nontrivial already on the original central scalars. -/
instance localDivisionSubfieldValuation_isNontrivial :
    (localDivisionSubfieldValuation K D ι).IsNontrivial := by
  obtain ⟨c, hc, hlt⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  apply (localDivisionSubfieldValuation K D ι).isNontrivial_iff_exists_lt_one.mpr
  refine ⟨algebraMap K L c, (map_ne_zero _).mpr hc, ?_⟩
  rw [localDivisionSubfieldValuation_apply, ι.commutes, localReducedNormValuation_algebraMap]
  exact pow_lt_one₀ zero_le hlt (CentralSimple.reducedDegree_pos K D).ne'

/-- Every finite embedded subfield is an actual nonarchimedean local field for this topology. -/
theorem localDivisionSubfieldIsLocalField [FiniteDimensional K L] :
    letI := localDivisionSubfieldNormedField K D ι
    letI := localDivisionSubfieldValuativeRel K D ι
    IsNonarchimedeanLocalField L := by
  let := localDivisionSubfieldNormedField K D ι
  let := localDivisionSubfieldNormedAlgebra K D ι
  let := localDivisionSubfieldValuativeRel K D ι
  let := localDivisionSubfield_ultrametric K D ι
  let : (localDivisionSubfieldValuation K D ι).Compatible :=
    Valuation.Compatible.ofValuation _
  let : (NormedField.valuation (K := L)).Compatible :=
    ⟨fun x y => (localDivisionSubfield_norm_le_iff K D ι x y).symm⟩
  let := NormedField.toValued (K := L)
  let : IsValuativeTopology L :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
      (fun {s} => Valued.mem_nhds_zero)
  let : ProperSpace L := FiniteDimensional.proper K L
  let : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (localDivisionSubfieldValuation K D ι)).mpr inferInstance
  exact { }

/-- The actual integer subring of the restricted valuation is Henselian. -/
theorem localDivisionSubfield_henselian [FiniteDimensional K L] :
    HenselianLocalRing (localDivisionSubfieldValuation K D ι).integer := by
  let := localDivisionSubfieldNormedField K D ι
  let := localDivisionSubfieldValuativeRel K D ι
  let := localDivisionSubfieldIsLocalField K D ι
  let : (localDivisionSubfieldValuation K D ι).Compatible :=
    Valuation.Compatible.ofValuation _
  have heq : (valuation L).integer = (localDivisionSubfieldValuation K D ι).integer := by
    ext x
    change valuation L x ≤ 1 ↔ localDivisionSubfieldValuation K D ι x ≤ 1
    rw [← (valuation L).map_one, ← (localDivisionSubfieldValuation K D ι).map_one]
    exact ValuativeRel.isEquiv (valuation L) (localDivisionSubfieldValuation K D ι) x 1
  have hH : HenselianLocalRing 𝒪[L] := by
    refine { is_henselian := ?_ }
    intro f hf a₀ hroot hder
    exact HenselianRing.is_henselian f hf a₀ hroot
      (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[L])))
  rw [← heq]
  exact hH

/-- A simple root in the actual strict-ideal residue lifts to an original integral root. -/
theorem localDivisionSubfield_hensel_lift [FiniteDimensional K L]
    (f : Polynomial (localDivisionSubfieldValuation K D ι).integer) (hf : f.Monic)
    (a₀ : DivisionValuation.Residue (localDivisionSubfieldValuation K D ι))
    (hroot : f.eval₂ (DivisionValuation.reduction _) a₀ = 0)
    (hder : f.derivative.eval₂ (DivisionValuation.reduction _) a₀ ≠ 0) :
    ∃ a : (localDivisionSubfieldValuation K D ι).integer,
      f.IsRoot a ∧ DivisionValuation.reduction _ a = a₀ := by
  let := localDivisionSubfield_henselian K D ι
  let : Field (DivisionValuation.Residue (localDivisionSubfieldValuation K D ι)) :=
    { DivisionValuation.residueDivisionRing _ with mul_comm := mul_comm }
  have hiff := (HenselianLocalRing.TFAE
    (localDivisionSubfieldValuation K D ι).integer).out 1 3
  exact hiff.mp (localDivisionSubfield_henselian K D ι)
    (DivisionValuation.reduction _) (DivisionValuation.reduction_surjective _) f hf a₀ hroot hder

end Langlands.CentralDivision
