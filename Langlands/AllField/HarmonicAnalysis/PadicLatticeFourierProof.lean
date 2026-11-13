import Langlands.HarmonicAnalysis.PadicLatticeFourierProof
import Langlands.AllField.HarmonicAnalysis.PadicLatticeFourierStatement
import Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof
/-!
# Plus-sign Fourier integrals of local-field lattice cosets

A coset of a compact open additive subgroup has a convergent plus-sign Fourier
integrand. Translation invariance moves the coset to the subgroup, and
orthogonality on the subgroup leaves its mass or zero. For the valuation lattice
`π^(-m) O` the annihilator is `π^(-(n-m)) O`, by the conductor API.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicRectangularHaarScalingStatement padicLatticeFourier padicLatticeGeometry padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u

section CompactOpenCoset

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

end CompactOpenCoset

end Langlands.AllField.HarmonicAnalysis

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicRectangularHaarScalingStatement padicLatticeFourier padicLatticeGeometry padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u
variable {F : Type u} [Field F] (T : LocalFieldData F)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F _ T.topology

/-- The `ψ`-annihilator of `π^(-m) O` is `π^(-(n(ψ)-m)) O`. -/
theorem forall_mul_eq_one_iff_mem_additiveLattice (ψ : AdditiveCharacter) (m : ℤ)
    (y : F) :
    (∀ t ∈ T.additiveLattice m, ψ (t * y) = 1) ↔
      y ∈ T.additiveLattice (T.additiveConductor ψ - m) := by
  constructor
  · intro h
    apply T.mem_additiveLattice_of_forall_mul_eq_one ψ m y
    intro x hx
    rw [mul_comm]
    exact h x hx
  · intro hy t ht
    apply (T.additiveConductor_spec ψ).1
    rw [mem_additiveLattice, map_mul]
    calc
      T.discreteValuation t * T.discreteValuation y ≤
          WithZero.exp m * WithZero.exp (T.additiveConductor ψ - m) :=
        mul_le_mul' ht hy
      _ = WithZero.exp (T.additiveConductor ψ) := by
        rw [← WithZero.exp_add, add_sub_cancel]

end Langlands.LocalFieldData

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicRectangularHaarScalingStatement padicLatticeFourier padicLatticeGeometry padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u

/-- The published lattice-coset Fourier proposition, for every supplied topology. -/
theorem padicLatticeFourier 
    (F : Type u) [Field F] (T : LocalFieldData F) :
    PadicLatticeFourierStatement F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ μ m a y C indicatorC
  refine ⟨coset_fourierIntegrand_integrable ψ μ (T.additiveLattice m)
    (T.isCompact_additiveLattice m) (T.isOpen_additiveLattice m) a y, ?_⟩
  rw [coset_fourierIntegral_eq]
  by_cases hy : y ∈ T.additiveLattice (T.additiveConductor ψ - m)
  · rw [subgroup_character_integral_of_trivial ψ μ (T.additiveLattice m)
      (T.isOpen_additiveLattice m) y
      ((T.forall_mul_eq_one_iff_mem_additiveLattice ψ m y).mpr hy),
      Set.indicator_of_mem (SetLike.mem_coe.mpr hy), mul_one, mul_comm]
  · have hnt : ¬ ∀ t ∈ T.additiveLattice m, ψ (t * y) = 1 :=
      fun h => hy ((T.forall_mul_eq_one_iff_mem_additiveLattice ψ m y).mp h)
    push Not at hnt
    obtain ⟨t₀, ht₀, hne⟩ := hnt
    rw [subgroup_character_integral_of_nontrivial ψ μ (T.additiveLattice m) y t₀ ht₀ hne,
      Set.indicator_of_notMem (fun h => hy (SetLike.mem_coe.mp h)), mul_zero, mul_zero]

end Langlands.AllField.HarmonicAnalysis
