import Langlands.Global.CanonicalIntegralModelCompletions
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.GroupScheme.IntegralModel.FieldFibers
import Langlands.GroupScheme.IntegralModel.LocalField

/-! # Good arithmetic models over canonical completion integers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel

namespace Langlands.Global.IntegralModelCompletions

open Langlands.GroupScheme
open Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

variable (F : Type u) [Field F] [NumberField F]
  (S : Finset (FinitePlace F)) (v : {v : FinitePlace F // v ∉ S})

local instance goodCompletionValuativeRel : ValuativeRel (FiniteCompletion F v.1) :=
  FiniteCompletion.valuativeRel v.1

local instance : Algebra ((S : Set (FinitePlace F)).integer F)
    𝒪[FiniteCompletion F v.1] := (canonicalIntegerMap F S v).toAlgebra

local instance : Algebra ((S : Set (FinitePlace F)).integer F)
    (FiniteCompletion F v.1) :=
  ((algebraMap F (FiniteCompletion F v.1)).comp
    (algebraMap ((S : Set (FinitePlace F)).integer F) F)).toAlgebra

local instance : SMul ((S : Set (FinitePlace F)).integer F) F :=
  (inferInstance : Algebra ((S : Set (FinitePlace F)).integer F) F).toSMul

local instance : SMul ((S : Set (FinitePlace F)).integer F) (FiniteCompletion F v.1) :=
  (inferInstance : Algebra ((S : Set (FinitePlace F)).integer F)
    (FiniteCompletion F v.1)).toSMul

local instance : IsScalarTower ((S : Set (FinitePlace F)).integer F)
    𝒪[FiniteCompletion F v.1] (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := 𝒪[FiniteCompletion F v.1]) (A := FiniteCompletion F v.1) fun _ => rfl

local instance : IsScalarTower ((S : Set (FinitePlace F)).integer F)
    F (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := F) (A := FiniteCompletion F v.1) fun _ => rfl

variable {G P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  (M : ModelData ((S : Set (FinitePlace F)).integer F) F p)

/-- Specialize the supplied simultaneous good models to the actual canonical
integers of the original finite completion. -/
def canonicalModelData :
    ModelData 𝒪[FiniteCompletion F v.1] (FiniteCompletion F v.1)
      ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).map p) := by
  let φ := M.inclusion.baseChangeCoefficients
    𝒪[FiniteCompletion F v.1] (FiniteCompletion F v.1)
  have hgood : GoodFieldFibers φ.hom :=
    M.goodFieldFibers.baseChange
      (Spec.map (CommRingCat.ofHom (canonicalIntegerMap F S v)))
  exact
    { ambient := canonicalModel F S v M.ambient
      parabolic := canonicalModel F S v M.parabolic
      inclusion := φ
      closedImmersion := M.inclusion.isClosedImmersion_baseChangeCoefficients
        _ _ M.closedImmersion
      reductive := hgood.isReductive
        (isSmooth_canonicalModel F S v M.ambient M.reductive.smooth) inferInstance
      parabolicSmooth := isSmooth_canonicalModel F S v M.parabolic M.parabolicSmooth
      fieldReductive := hgood.reductive
      fieldParabolic := hgood.parabolic
      fieldConnected := hgood.connected }

/-- The ambient model retains the already specified canonical generic comparison. -/
theorem canonicalModelData_ambient :
    (canonicalModelData F S v M).ambient = canonicalModel F S v M.ambient :=
  rfl

/-- The subgroup model retains the already specified canonical generic comparison. -/
theorem canonicalModelData_parabolic :
    (canonicalModelData F S v M).parabolic = canonicalModel F S v M.parabolic :=
  rfl

/-- The inclusion is the pullback of the original inclusion along the actual
S-integer map into the canonical valuation ring. -/
theorem canonicalModelData_inclusion_hom :
    (canonicalModelData F S v M).inclusion.hom =
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (canonicalIntegerMap F S v)))).map M.inclusion.hom :=
  rfl

/-- The actual residue quotient gives a connected reductive ambient special
fibre and a parabolic inclusion with connected source special fibre. -/
theorem canonicalModelData_specialFibre :
    IsConnectedReductive (canonicalModelData F S v M).ambient.specialFibre ∧
      IsParabolicSubgroup (canonicalModelData F S v M).inclusion.specialFibreMap ∧
      (canonicalModelData F S v M).parabolic.HasConnectedSpecialFibre :=
  (canonicalModelData F S v M).goodFieldFibers.atFieldPoint
    𝓀[FiniteCompletion F v.1] (IntegralModel.residueBaseMap 𝒪[FiniteCompletion F v.1])

end Langlands.Global.IntegralModelCompletions
