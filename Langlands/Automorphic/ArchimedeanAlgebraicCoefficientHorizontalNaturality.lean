import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientHorizontalTransport
import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticHorizontalTransport
import Langlands.Cohomology.Lie.HorizontalCohomologyNaturality

/-! # Naturality of the actual analytic and algebraic coefficient comparison -/

noncomputable section

universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme
open Langlands.Cohomology.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

local instance coefficientNaturalityRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance coefficientNaturalityContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientNaturalitySmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientNaturalityFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance coefficientNaturalityStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable {S T : OperatorRealization F n}

local instance coefficientNaturalitySpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The original coefficient comparison commutes with an arbitrary full
operator intertwiner on the automorphic tensor factor. -/
theorem tensorAnalyticAlgebraicReducedLieEquiv_natural (L : S.Intertwiner T)
    (v : S.Space ⊗[ℂ] AnalyticSpace e ρ) :
    tensorAnalyticAlgebraicReducedLieEquiv e ρ T
        (tensorAnalyticIntertwinerReducedLieHom e ρ L v) =
      tensorAlgebraicIntertwinerReducedLieHom e ρ L
        (tensorAnalyticAlgebraicReducedLieEquiv e ρ S v) := by
  change TensorProduct.map (LinearMap.id : T.Space →ₗ[ℂ] T.Space)
      (analyticCoordinates e ρ).toLinearMap
      (TensorProduct.map L.toLinearMap
        (LinearMap.id : AnalyticSpace e ρ →ₗ[ℂ] AnalyticSpace e ρ) v) =
    TensorProduct.map L.toLinearMap (LinearMap.id : Space e ρ →ₗ[ℂ] Space e ρ)
      (TensorProduct.map (LinearMap.id : S.Space →ₗ[ℂ] S.Space)
        (analyticCoordinates e ρ).toLinearMap v)
  exact LinearMap.congr_fun
    ((LinearMap.lTensor_comp_rTensor S.Space L.toLinearMap (analyticCoordinates e ρ).toLinearMap).trans
      (LinearMap.rTensor_comp_lTensor S.Space L.toLinearMap (analyticCoordinates e ρ).toLinearMap).symm) v

/-- Naturality on the original full horizontal cochain finite representations. -/
theorem tensorAnalyticAlgebraicHorizontalEquiv_natural (L : S.Intertwiner T) (q : ℕ) :
    (tensorAnalyticAlgebraicHorizontalEquiv e ρ T q).toIntertwiningMap.comp
        (tensorAnalyticHorizontalMap e ρ L q) =
      (tensorAlgebraicHorizontalMap e ρ L q).comp
        (tensorAnalyticAlgebraicHorizontalEquiv e ρ S q).toIntertwiningMap := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  exact tensorAnalyticAlgebraicReducedLieEquiv_natural e ρ L (f.val X)


variable [NeZero n]

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "τAS" => S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "τAT" => T.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "τBS" => S.tensorCompactRepresentation (compactRepresentation e ρ)
local notation "τBT" => T.tensorCompactRepresentation (compactRepresentation e ρ)
local notation "hτAS" => tensorAnalyticCompactRepresentation_reduced_lie e ρ S
local notation "hτAT" => tensorAnalyticCompactRepresentation_reduced_lie e ρ T
local notation "hτBS" => tensorAlgebraicCompactRepresentation_reduced_lie e ρ S
local notation "hτBT" => tensorAlgebraicCompactRepresentation_reduced_lie e ρ T
local notation "hιAS" => tensorAnalyticHorizontal_infinitesimal e ρ S
local notation "hιAT" => tensorAnalyticHorizontal_infinitesimal e ρ T
local notation "hιBS" => tensorAlgebraicHorizontal_infinitesimal e ρ S
local notation "hιBT" => tensorAlgebraicHorizontal_infinitesimal e ρ T
local notation "AAS" => S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "AAT" => T.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "ABS" => S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ)
local notation "ABT" => T.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ)
local notation "hAAS" => tensorAnalyticHorizontalDifferential_finite e ρ S
local notation "hAAT" => tensorAnalyticHorizontalDifferential_finite e ρ T
local notation "hABS" => tensorAlgebraicHorizontalDifferential_finite e ρ S
local notation "hABT" => tensorAlgebraicHorizontalDifferential_finite e ρ T
local notation "aS" => (fun q => Representation.Equiv.toIntertwiningMap (tensorAnalyticAlgebraicHorizontalEquiv e ρ S q))
local notation "aT" => (fun q => Representation.Equiv.toIntertwiningMap (tensorAnalyticAlgebraicHorizontalEquiv e ρ T q))
local notation "haS" => tensorAnalyticAlgebraicHorizontalDifferential e ρ S
local notation "haT" => tensorAnalyticAlgebraicHorizontalDifferential e ρ T

/-- The actual comparison and full automorphic maps form a bundled square
on the original cycle representations. -/
abbrev tensorAnalyticAlgebraicHorizontalCyclesSquare (L : S.Intertwiner T) (q : ℕ) :=
  Horizontal.mapCyclesIntertwinerSquare H σ τAS τAT hσ hτAS hτAT hιAS hιAT
    AAS AAT hAAS hAAT (tensorAnalyticHorizontalMap e ρ L)
    (tensorAnalyticHorizontalMap_differential e ρ L)
    τBS hτBS hιBS ABS hABS τBT hτBT hιBT ABT hABT
    aT haT aS haS (tensorAlgebraicHorizontalMap e ρ L)
    (tensorAlgebraicHorizontalMap_differential e ρ L)
    (tensorAnalyticAlgebraicHorizontalEquiv_natural e ρ L) q

/-- The same actual square on the original cycle quotients. -/
abbrev tensorAnalyticAlgebraicHorizontalCohomologySquare (L : S.Intertwiner T) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwinerSquare H σ τAS τAT hσ hτAS hτAT hιAS hιAT
    AAS AAT hAAS hAAT (tensorAnalyticHorizontalMap e ρ L)
    (tensorAnalyticHorizontalMap_differential e ρ L)
    τBS hτBS hιBS ABS hABS τBT hτBT hιBT ABT hABT
    aT haT aS haS (tensorAlgebraicHorizontalMap e ρ L)
    (tensorAlgebraicHorizontalMap_differential e ρ L)
    (tensorAnalyticAlgebraicHorizontalEquiv_natural e ρ L) q

/-- Naturality of the original cycle comparison for full automorphic maps. -/
abbrev tensorAnalyticAlgebraicHorizontalCyclesEquiv_natural (L : S.Intertwiner T) (q : ℕ) :=
  Horizontal.mapCyclesIntertwiner_square H σ τAS τAT hσ hτAS hτAT hιAS hιAT
    AAS AAT hAAS hAAT (tensorAnalyticHorizontalMap e ρ L)
    (tensorAnalyticHorizontalMap_differential e ρ L)
    τBS hτBS hιBS ABS hABS τBT hτBT hιBT ABT hABT
    aT haT aS haS (tensorAlgebraicHorizontalMap e ρ L)
    (tensorAlgebraicHorizontalMap_differential e ρ L)
    (tensorAnalyticAlgebraicHorizontalEquiv_natural e ρ L) q

/-- Naturality of the original cohomology comparison for full automorphic maps. -/
abbrev tensorAnalyticAlgebraicHorizontalCohomologyEquiv_natural (L : S.Intertwiner T) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwiner_square H σ τAS τAT hσ hτAS hτAT hιAS hιAT
    AAS AAT hAAS hAAT (tensorAnalyticHorizontalMap e ρ L)
    (tensorAnalyticHorizontalMap_differential e ρ L)
    τBS hτBS hιBS ABS hABS τBT hτBT hιBT ABT hABT
    aT haT aS haS (tensorAlgebraicHorizontalMap e ρ L)
    (tensorAlgebraicHorizontalMap_differential e ρ L)
    (tensorAnalyticAlgebraicHorizontalEquiv_natural e ρ L) q

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
