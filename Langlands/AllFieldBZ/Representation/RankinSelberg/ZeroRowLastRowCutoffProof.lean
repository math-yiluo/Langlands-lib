import Langlands.AllFieldBZ.Group.GL.RankMaps
import Langlands.AllFieldBZ.HarmonicAnalysis.PadicLatticeTopology
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof

/-!
# All-field port of `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe u
variable {F : LocalFieldPackage.{u}} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- If `x ↦ ψ(a x)` is trivial on `π^(-m) O`, then `a` lies in `π^(m - n(ψ)) O`. -/
theorem mem_additiveLattice_of_forall_mul_eq_one (ψ : AdditiveCharacter)
    (m : ℤ) (a : F.Carrier) (h : ∀ x ∈ T.additiveLattice m, ψ (a * x) = 1) :
    a ∈ T.additiveLattice (T.additiveConductor ψ - m) := by
  have hπ : T.uniformizer ^ (-m) ≠ 0 := by
    apply zpow_ne_zero
    apply T.discreteValuation.ne_zero_iff.mp
    rw [T.discreteValuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hlevel : T.additiveConductor ψ - m =
      T.additiveConductor ψ + T.ord (T.uniformizer ^ (-m)) := by
    rw [T.ord_zpow, T.ord_uniformizer, mul_one, sub_eq_add_neg]
  rw [hlevel]
  apply (T.mul_mem_additiveLattice_iff hπ _ a).mp
  apply (T.integer_annihilator_iff_mem_additiveLattice ψ _).mp
  intro t
  have ht : T.uniformizer ^ (-m) * (t : F.Carrier) ∈ T.additiveLattice m :=
    (T.mem_additiveLattice_iff_exists_integer m _).mpr ⟨t, rfl⟩
  have hprod : (t : F.Carrier) * (T.uniformizer ^ (-m) * a) =
      a * (T.uniformizer ^ (-m) * (t : F.Carrier)) := by ring
  rw [hprod]
  exact h _ ht

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.RankinSelberg
open Langlands.RankinSelberg
open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Topology
open scoped Matrix
universe uF uV

section Column
variable {F : Type uF} [Field F]

section Topology
variable [TopologicalSpace F]

variable [IsTopologicalRing F]

end Topology
end Column
end Langlands.AllFieldBZ.RankinSelberg
