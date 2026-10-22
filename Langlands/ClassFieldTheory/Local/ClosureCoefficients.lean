import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.Cohomology.Continuous.CochainComparison
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.MulAction

/-! # Actual closure-stage coefficient maps

The source cohomology in this file is continuous cohomology of a finite
Galois group. Its ordinary-cohomology comparison is a separate construction.
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- The actual action on discrete units is jointly continuous, not merely
continuous for each fixed automorphism. -/
theorem continuous_unitAction (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] :
    Continuous (fun gx : Gal(L/K) × discreteUnitsRepresentation K L =>
      (discreteUnitsRepresentation K L).ρ gx.1 gx.2) := by
  let : MulAction Gal(L/K) (discreteUnitsRepresentation K L) := {
    smul σ x := (discreteUnitsRepresentation K L).ρ σ x
    one_smul x := by
      exact congrArg (fun f => f x)
        (discreteUnitsRepresentation K L).ρ.toRepresentation.map_one
    mul_smul σ τ x := by
      exact congrArg (fun f => f x)
        ((discreteUnitsRepresentation K L).ρ.toRepresentation.map_mul σ τ) }
  have hstab (x : discreteUnitsRepresentation K L) :
      IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
    have heq : (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) =
        (unitOpenStabilizer K L (Additive.toMul (x : Additive Lˣ)) : Set Gal(L/K)) := by
      ext σ
      exact (mem_unitOpenStabilizer_iff K L (x : Additive Lˣ) σ).symm
    rw [heq]
    exact (unitOpenStabilizer K L (Additive.toMul (x : Additive Lˣ))).isOpen
  let : ContinuousSMul Gal(L/K) (discreteUnitsRepresentation K L) :=
    continuousSMul_iff_stabilizer_isOpen.mpr hstab
  exact continuous_smul

/-- The actual continuous-to-ordinary comparison for the discrete Galois unit
module. This definition does not assert or assume invertibility. -/
def continuousToRelative (K : Type v) (L : Type u)
    [Field K] [Field L] [Algebra K L] (n : ℕ) :
    continuousCohomology n (discreteUnitsRepresentation K L) →+
      relativeCohomology K L n :=
  (Langlands.Continuous.continuousToOrdinary
    (discreteUnitsRepresentation K L) n).hom.toAddMonoidHom

variable (K : Type u) [Field K]
variable (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]

/-- Restriction from the actual absolute Galois group to a normal intermediate field. -/
def closureRestriction : Field.absoluteGaloisGroup K →ₜ* Gal(E/K) where
  __ := AlgEquiv.restrictNormalHom E
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous E

/-- Actual inclusion of intermediate-field units into closure units,
equivariant for the same continuous restriction homomorphism. -/
def closureInflationCoefficients :
    TopRep.res (closureRestriction K E)
      (discreteUnitsRepresentation K E) ⟶ absoluteUnits K where
  hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := unitInclusionLinear E (AlgebraicClosure K)
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact AlgEquiv.restrictNormal_commutes σ E x.val }

/-- Genuine continuous inflation from a normal intermediate field into the closure.
For a finite intermediate field, the source group has its finite discrete Krull topology. -/
abbrev closureContinuousInflation (n : ℕ) :
    continuousCohomology n (discreteUnitsRepresentation K E) ⟶
      absoluteCohomology K n :=
  ContinuousCohomology.map (closureRestriction K E)
    (closureInflationCoefficients K E) n

end Langlands.ClassFieldTheory.Local
