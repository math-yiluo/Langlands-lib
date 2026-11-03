import Langlands.Representation.Plancherel.DiscreteSeriesOrbits
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-! # Quotient topology on discrete-series twist orbits -/

noncomputable section

open Topology
open scoped NNReal

namespace Langlands.Plancherel

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (mu : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure mu]
variable {I : Type uI} (nu : I → (G →* ℝ≥0ˣ))

/-- Give the actual twist orbit the topology of its stabilizer quotient.
This does not put a topology on the entire smooth dual. -/
instance discreteSeriesOrbitTopologicalSpace (omega : DiscreteSeriesClass A hA mu) :
    TopologicalSpace (discreteSeriesOrbit A hA mu nu omega) :=
  TopologicalSpace.induced (discreteSeriesOrbitEquiv A hA mu nu omega).symm inferInstance

/-- The existing actual orbit-stabilizer bijection, with its quotient topology. -/
def discreteSeriesOrbitHomeomorph (omega : DiscreteSeriesClass A hA mu) :
    ((unitaryUnramifiedCharacters nu) ⧸ discreteSeriesStabilizer A hA mu nu omega) ≃ₜ
      discreteSeriesOrbit A hA mu nu omega :=
  ((discreteSeriesOrbitEquiv A hA mu nu omega).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp]
theorem discreteSeriesOrbitHomeomorph_mk
    (omega : DiscreteSeriesClass A hA mu) (chi : unitaryUnramifiedCharacters nu) :
    (discreteSeriesOrbitHomeomorph A hA mu nu omega (QuotientGroup.mk chi)).val =
      chi • omega := rfl

/-- The actual twisting map, with codomain restricted to its orbit. -/
def discreteSeriesOrbitMap (omega : DiscreteSeriesClass A hA mu) :
    unitaryUnramifiedCharacters nu → discreteSeriesOrbit A hA mu nu omega :=
  fun chi => discreteSeriesOrbitHomeomorph A hA mu nu omega (QuotientGroup.mk chi)

@[simp]
theorem discreteSeriesOrbitMap_val
    (omega : DiscreteSeriesClass A hA mu) (chi : unitaryUnramifiedCharacters nu) :
    (discreteSeriesOrbitMap A hA mu nu omega chi).val = chi • omega := rfl

/-- An orbit is the open quotient of the compact-open character group by its
actual stabilizer. -/
theorem isOpenQuotientMap_discreteSeriesOrbitMap
    (omega : DiscreteSeriesClass A hA mu) :
    IsOpenQuotientMap (discreteSeriesOrbitMap A hA mu nu omega) :=
  (discreteSeriesOrbitHomeomorph A hA mu nu omega).isOpenQuotientMap.comp
    QuotientGroup.isOpenQuotientMap_mk

theorem continuous_discreteSeriesOrbitMap
    (omega : DiscreteSeriesClass A hA mu) :
    Continuous (discreteSeriesOrbitMap A hA mu nu omega) :=
  (isOpenQuotientMap_discreteSeriesOrbitMap A hA mu nu omega).continuous

/-- Compactness needs only compactness of the actual unitary character group. -/
theorem compactSpace_discreteSeriesOrbit [CompactSpace (unitaryUnramifiedCharacters nu)]
    (omega : DiscreteSeriesClass A hA mu) :
    CompactSpace (discreteSeriesOrbit A hA mu nu omega) :=
  (discreteSeriesOrbitHomeomorph A hA mu nu omega).compactSpace

/-- A finite actual stabilizer is closed, so its character quotient and orbit
are Hausdorff. -/
theorem t2Space_discreteSeriesOrbit (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)] :
    T2Space (discreteSeriesOrbit A hA mu nu omega) := by
  let : IsClosed (discreteSeriesStabilizer A hA mu nu omega :
      Set (unitaryUnramifiedCharacters nu)) := (Set.toFinite _).isClosed
  exact (discreteSeriesOrbitHomeomorph A hA mu nu omega).t2Space

/-- Changing the orbit's base point by a character gives the identity on
underlying representation classes as a homeomorphism. -/
def discreteSeriesOrbitBaseChange (omega : DiscreteSeriesClass A hA mu)
    (chi : unitaryUnramifiedCharacters nu) :
    discreteSeriesOrbit A hA mu nu (chi • omega) ≃ₜ
      discreteSeriesOrbit A hA mu nu omega where
  toEquiv := Set.equivOfEq (MulAction.orbit_smul chi omega)
  continuous_toFun := by
    apply (isOpenQuotientMap_discreteSeriesOrbitMap A hA mu nu (chi • omega)
      ).isQuotientMap.continuous_iff.mpr
    convert (continuous_discreteSeriesOrbitMap A hA mu nu omega).comp
      (continuous_id.mul_const chi) using 1
    funext eta
    apply Subtype.ext
    exact (mul_smul eta chi omega).symm
  continuous_invFun := by
    apply (isOpenQuotientMap_discreteSeriesOrbitMap A hA mu nu omega
      ).isQuotientMap.continuous_iff.mpr
    convert (continuous_discreteSeriesOrbitMap A hA mu nu (chi • omega)).comp
      (continuous_id.mul_const chi⁻¹) using 1
    funext eta
    apply Subtype.ext
    change eta • omega = (eta * chi⁻¹) • (chi • omega)
    simp only [mul_smul, inv_smul_smul]

@[simp]
theorem discreteSeriesOrbitBaseChange_val (omega : DiscreteSeriesClass A hA mu)
    (chi : unitaryUnramifiedCharacters nu)
    (eta : discreteSeriesOrbit A hA mu nu (chi • omega)) :
    (discreteSeriesOrbitBaseChange A hA mu nu omega chi eta).val = eta.val := rfl

@[simp]
theorem discreteSeriesOrbitBaseChange_symm_val (omega : DiscreteSeriesClass A hA mu)
    (chi : unitaryUnramifiedCharacters nu)
    (eta : discreteSeriesOrbit A hA mu nu omega) :
    ((discreteSeriesOrbitBaseChange A hA mu nu omega chi).symm eta).val = eta.val := rfl

end Langlands.Plancherel
