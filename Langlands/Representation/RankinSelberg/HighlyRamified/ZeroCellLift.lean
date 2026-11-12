import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Representation.RankinSelberg.UnramifiedKirillovInjectivity
import Langlands.Representation.Conductor.EssentialUniquenessReduction
import Langlands.Representation.Conductor.EssentialDualSetup

/-!
# Zero-cell Kirillov lifts are fixed by the integral mirabolic group

For a generic representation `π` of `GL_(n+2)(F)` over a p-adic field, the restriction of
`v ↦ (g ↦ ℓ(π(g) v))` to the mirabolic subgroup is injective (the Kirillov injectivity
theorem together with multiplicity one). A model vector agreeing on the mirabolic subgroup
with the zero-cell function `W₀` is therefore fixed by the integral mirabolic group
`H(0) = GL_(n+2)(O) ∩ P`: for `h ∈ H(0)` the translate by `h` agrees with `W₀` on the
mirabolic subgroup as well, because `W₀` is right `GL_(n+2)(O)`-invariant.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open Langlands.GeneralLinear.Iwasawa

universe uF uV

section Fixed

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
  {ψ : UnitaryAdditiveCharacter F} (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1 + 1) F) V)
  (ℓ : glFunctionals ψ (n + 1) π)

/-- Under mirabolic restriction injectivity, a model vector that agrees with the zero-cell
function on the mirabolic subgroup is fixed by the integral mirabolic group `H(0)`. -/
theorem mem_fixedVectors_fieldJacquetMirabolic_of_zeroCell
    (hinj : Conductor.IsMirabolicRestrictionInjective π ℓ)
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : ∀ g : Langlands.GeneralLinear (n + 1 + 1) F,
      (∀ j, g.val (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then 1 else 0) →
      w.val.val g = (zeroCellWhittaker hϖ hψ (n + 1)).val g) :
    w ∈ fixedVectors (modelRepresentation π ℓ)
      (Conductor.fieldJacquetMirabolic (ValuativeRel.valuation F).integer (n + 1)) := by
  apply Conductor.mem_fixedVectors_of_levi_restriction ψ π ℓ
    (Conductor.modelMirabolicRestriction_injective_of_carrier ψ π ℓ hinj) _ w
  intro h hh g
  have hm : rankInclusion 1 g * h ∈ mirabolic (n + 1) F :=
    (mirabolic (n + 1) F).mul_mem (rankInclusion_lastRow g) hh.2
  rw [hw _ hm, hw _ (rankInclusion_lastRow g)]
  exact zeroCellWhittaker_mul_integral hϖ hψ (n + 1) _ hh.1

/-- The same invariance, stated pointwise. -/
theorem zeroCell_mul_fieldJacquetMirabolic
    (hinj : Conductor.IsMirabolicRestrictionInjective π ℓ)
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : ∀ g : Langlands.GeneralLinear (n + 1 + 1) F,
      (∀ j, g.val (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then 1 else 0) →
      w.val.val g = (zeroCellWhittaker hϖ hψ (n + 1)).val g)
    (k : Langlands.GeneralLinear (n + 1 + 1) F)
    (hk : k ∈ Conductor.fieldJacquetMirabolic (ValuativeRel.valuation F).integer (n + 1))
    (g : Langlands.GeneralLinear (n + 1 + 1) F) :
    w.val.val (g * k) = w.val.val g := by
  have h := (mem_fixedVectors_fieldJacquetMirabolic_of_zeroCell hϖ hψ π ℓ hinj w hw) ⟨k, hk⟩
  exact congrArg (fun z : (coefficientModel π ℓ).toSubmodule => z.val.val g) h

end Fixed

section Injective

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

attribute [local instance] Unramified.heckeFieldTopology Unramified.heckeFieldValuativeRel
  Unramified.heckeFieldLocalField

/-- Kirillov injectivity for a generic representation of `GL_(n+2)(F)`: the vector `v` is
determined by the restriction of `g ↦ ℓ(π(g) v)` to the mirabolic subgroup. -/
theorem isMirabolicRestrictionInjective_of_isGeneric
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1 + 1) F.Carrier) V)
    (hπ : Whittaker.IsGeneric ψ (n + 1) π)
    (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0) :
    Conductor.IsMirabolicRestrictionInjective π ℓ := by
  obtain ⟨hirr, hadm, -⟩ := hπ
  have hmult : ∀ ℓ' : glFunctionals ψ (n + 1) π, ∃ c : ℂ, ℓ' = c • ℓ := by
    intro ℓ'
    obtain ⟨c, hc, -⟩ :=
      Whittaker.multiplicityOne p inferInstance F (n + 1) V ψ π hadm hirr ℓ ℓ' hℓ
    exact ⟨c, hc⟩
  intro v v' hvv
  rw [← sub_eq_zero]
  apply UnramifiedUnitary.kirillov_injective F.canonicalTopologicalData ψ (n + 1) π hadm.1
    hirr ℓ hℓ hmult
  intro g
  have h := congrFun hvv g
  simp only at h
  rw [map_sub, map_sub, h, sub_self]

/-- A zero-cell Kirillov lift: every nonzero Whittaker functional of a generic `π` has a
model vector agreeing with the zero-cell function on the mirabolic subgroup. -/
theorem exists_zeroCellLift
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {ϖ : F.Carrierˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ)
    (hψ : ∀ x ∈ (ValuativeRel.valuation F.Carrier).integer, ψ x = 1)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1 + 1) F.Carrier) V)
    (hπ : Whittaker.IsGeneric ψ (n + 1) π)
    (ℓ : glFunctionals ψ (n + 1) π) (hℓ : ℓ.val ≠ 0) :
    ∃ w : (coefficientModel π ℓ).toSubmodule,
      ∀ g : Langlands.GeneralLinear (n + 1 + 1) F.Carrier,
        (∀ j, g.val (Fin.last (n + 1)) j = if j = Fin.last (n + 1) then 1 else 0) →
        w.val.val g = (zeroCellWhittaker hϖ hψ (n + 1)).val g :=
  Whittaker.modelKirillovTransfer whittakerTypeKirillov p inferInstance F
    F.canonicalTopologicalData (n + 1) V π ψ (isOfWhittakerType_of_isGeneric F hπ) ℓ hℓ
    (zeroCellWhittaker hϖ hψ (n + 1)) (isMirabolicTestFunction_zeroCellWhittaker hϖ hψ (n + 1))

end Injective

end Langlands.RankinSelberg.HighlyRamified
