import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.AllField.HarmonicAnalysis.PadicLatticeTopology
/-!
# Additive lattices and the conductor of an additive character

The all-field form of the lattice lemma from the p-adic module
`Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`: if `x ↦ ψ(a x)` is trivial
on `π^(-m) O`, then `a` lies in `π^(m - n(ψ)) O`. The field-generic column lemmas of that
module are used from the original, which this module imports. Its main theorem
`zeroRowLastRowCutoff` is not needed by the unequal-rank functional equation and is not ported.
-/

noncomputable section

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u
variable {F : Type u} [Field F] (T : LocalFieldData F)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F _ T.topology

/-- If `x ↦ ψ(a x)` is trivial on `π^(-m) O`, then `a` lies in `π^(m - n(ψ)) O`. -/
theorem mem_additiveLattice_of_forall_mul_eq_one (ψ : AdditiveCharacter)
    (m : ℤ) (a : F) (h : ∀ x ∈ T.additiveLattice m, ψ (a * x) = 1) :
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
  have ht : T.uniformizer ^ (-m) * (t : F) ∈ T.additiveLattice m :=
    (T.mem_additiveLattice_iff_exists_integer m _).mpr ⟨t, rfl⟩
  have hprod : (t : F) * (T.uniformizer ^ (-m) * a) =
      a * (T.uniformizer ^ (-m) * (t : F)) := by ring
  rw [hprod]
  exact h _ ht

end Langlands.LocalFieldData
