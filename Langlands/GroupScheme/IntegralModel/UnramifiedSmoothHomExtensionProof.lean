import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.ValuedCoefficientDescent
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Extension of generic homomorphisms from maximal-unramified integral points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open scoped ValuativeRel

namespace Langlands.GroupScheme.IntegralModel

/-- KP Corollary 2.10.10 and the second part of Remark 2.10.19 over a
nonarchimedean local field, tested on maximal-unramified integral points. -/
theorem unramifiedSmoothHomExtension : UnramifiedSmoothHomExtensionStatement.{u} := by
  intro F _ _ _ _ G H f M N hM hf
  let : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
    Valuation.HasExtension.instAlgebraInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
  let : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
    Valuation.HasExtension.instIsScalarTowerInteger
      (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  obtain ⟨φ⟩ := smoothHomExtension (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G) (baseChanged F (inertiaFixedField F) H)
    ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map f)
    M.baseChangeUnramified N.baseChangeUnramified
    (M.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F) hM) hf
  exact ⟨(Hom.valuationCoefficientEquiv
    (ValuativeRel.valuation F) (fixedFieldValuation F)).symm φ⟩

end Langlands.GroupScheme.IntegralModel
