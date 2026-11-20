import Langlands.LocalField.ContinuousIntegerTransport
import Langlands.BaseChange.ExtensionInvariants
import Langlands.AllField.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction
import Langlands.HarmonicAnalysis.CharacterTransport

/-!
# The conductor of a trace character

The trace codifferent is the valuation lattice of triviality for the pullback
of a character of conductor zero.
-/

noncomputable section

open scoped WithZero

namespace Langlands.BaseChange

open HarmonicAnalysis (UnitaryAdditiveCharacter)

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E]

/-- The different exponent identifies the trace codifferent with the actual
valuation lattice at that level. -/
theorem IsDifferentExponent.mem_additiveLattice_iff {d : ℕ}
    (hd : IsDifferentExponent F E d) (x : E) :
    x ∈ (LocalFieldData.ofInstances E).additiveLattice (d : ℤ) ↔
      ∀ y ∈ (LocalFieldData.ofInstances E).Integers,
        Algebra.trace F E (x * y) ∈ (LocalFieldData.ofInstances F).Integers := by
  obtain ⟨ϖ, hϖ, hcod⟩ := hd
  let TE := LocalFieldData.ofInstances E
  refine Iff.trans ?_ (hcod x).symm
  change x ∈ TE.additiveLattice (d : ℤ) ↔ x * (ϖ : E) ^ d ∈ TE.Integers
  rw [TE.mem_additiveLattice, TE.mem_integers_iff_discreteValuation_le_one, map_mul, map_pow,
    AllField.RankinSelberg.discreteValuation_of_isUniformizingElement hϖ, ← WithZero.exp_nsmul]
  have hp : WithZero.exp (d : ℤ) * WithZero.exp (d • (-1 : ℤ)) = 1 := by
    rw [← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp
  rw [← hp]
  exact (mul_le_mul_iff_left₀ (WithZero.exp_pos (a := d • (-1 : ℤ)))).symm

/-- If `ψE` is the field-trace pullback of a character of additive conductor
zero, its additive conductor is the different exponent. -/
theorem IsDifferentExponent.additiveConductor_of_trace
    [IsModuleTopology F E] {d : ℕ} (hd : IsDifferentExponent F E d)
    (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E)
    (hψ : (LocalFieldData.ofInstances F).additiveConductor ψF = 0)
    (htrace : ∀ x : E, ψE x = ψF (Algebra.trace F E x)) :
    (LocalFieldData.ofInstances E).additiveConductor ψE = (d : ℤ) := by
  let TF := LocalFieldData.ofInstances F
  let TE := LocalFieldData.ofInstances E
  have halg (a : TF.Integers) : algebraMap F E a ∈ TE.Integers :=
    TF.map_mem_integers_of_continuous TE (algebraMap F E)
      (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E)) a.property
  have hcod (x : E) :
      (∀ t : TE.Integers, ψE ((t : E) * x) = 1) ↔
        ∀ y ∈ TE.Integers, Algebra.trace F E (x * y) ∈ TF.Integers := by
    constructor
    · intro h y hy
      have hann := TF.integer_annihilator_iff_mem_additiveLattice ψF (Algebra.trace F E (x * y))
      rw [hψ, TF.mem_additiveLattice_zero] at hann
      apply hann.mp
      intro a
      have hz := h ⟨algebraMap F E a * y, mul_mem (halg a) hy⟩
      change ψE ((algebraMap F E a * y) * x) = 1 at hz
      rw [htrace, mul_assoc, mul_comm y x, ← Algebra.smul_def, map_smul, smul_eq_mul] at hz
      exact hz
    · intro h t
      rw [htrace, mul_comm (t : E) x]
      apply (TF.additiveTrivialAt_iff_le_conductor ψF 0).mpr (by rw [hψ])
      exact (TF.mem_additiveLattice_zero _).mpr (h t t.property)
  have hmem (x : E) : x ∈ TE.additiveLattice (TE.additiveConductor ψE) ↔
      x ∈ TE.additiveLattice (d : ℤ) :=
    (TE.integer_annihilator_iff_mem_additiveLattice ψE x).symm.trans
      ((hcod x).trans (hd.mem_additiveLattice_iff x).symm)
  obtain ⟨x, hx⟩ := TE.discreteValuation_surjective (WithZero.exp (TE.additiveConductor ψE))
  obtain ⟨y, hy⟩ := TE.discreteValuation_surjective (WithZero.exp (d : ℤ))
  apply le_antisymm
  · have hxmem := (hmem x).mp (TE.mem_additiveLattice _ _ |>.mpr hx.le)
    exact WithZero.exp_le_exp.mp ((hx ▸ (TE.mem_additiveLattice _ _).mp hxmem))
  · have hymem := (hmem y).mpr (TE.mem_additiveLattice _ _ |>.mpr hy.le)
    exact WithZero.exp_le_exp.mp ((hy ▸ (TE.mem_additiveLattice _ _).mp hymem))

end Langlands.BaseChange
