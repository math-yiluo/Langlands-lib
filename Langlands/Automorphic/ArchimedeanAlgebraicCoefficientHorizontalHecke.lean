import Langlands.Automorphic.HorizontalFiniteHecke
import Langlands.Cohomology.Lie.HorizontalCohomologyHeckeEquivalence
import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientHorizontalComparison

/-! # Original coefficient cohomology with finite Hecke actions -/

noncomputable section

universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic.ArchimedeanAlgebraicCoefficient

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.GroupScheme
open Langlands.Cohomology.Lie MeasureTheory

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {I : Type} [Fintype I] (e : I → EmbeddingIndex F)
variable {m : Type} [Fintype m] [DecidableEq m]
variable (ρ : MatrixRepresentation
  (GeneralLinearProductDualNumber.groupScheme (fun _ : I => Fin n)
    (CommRingCat.of ℂ)) m)

local instance coefficientHeckeRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance coefficientHeckeContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientHeckeSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientHeckeFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance coefficientHeckeStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (S : OperatorRealization F n)

local instance coefficientHeckeSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

variable [NeZero n]

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "τa" => S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "τb" => S.tensorCompactRepresentation (compactRepresentation e ρ)
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hτa" => tensorAnalyticCompactRepresentation_reduced_lie e ρ S
local notation "hτb" => tensorAlgebraicCompactRepresentation_reduced_lie e ρ S
local notation "hιa" => tensorAnalyticHorizontal_infinitesimal e ρ S
local notation "hιb" => tensorAlgebraicHorizontal_infinitesimal e ρ S
local notation "Aa" => S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "Ab" => S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ)
local notation "hAa" => tensorAnalyticHorizontalDifferential_finite e ρ S
local notation "hAb" => tensorAlgebraicHorizontalDifferential_finite e ρ S
local notation "sa" => S.tensorHorizontalFiniteRepresentation_isSmooth
  (analyticCompactRepresentation e ρ)
local notation "sb" => S.tensorHorizontalFiniteRepresentation_isSmooth
  (compactRepresentation e ρ)

/-- Smoothness of the original analytic closed cochains. -/
abbrev tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth (q : ℕ) :=
  Horizontal.cyclesRepresentation_isSmooth H σ τa hσ hτa hιa Aa hAa sa q

/-- Smoothness of the original analytic cycle quotient. -/
abbrev tensorAnalyticHorizontalCohomologyFiniteRepresentation_isSmooth (q : ℕ) :=
  Horizontal.cohomologyRepresentation_isSmooth H σ τa hσ hτa hιa Aa hAa sa q

/-- Smoothness of the original algebraic closed cochains. -/
abbrev tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth (q : ℕ) :=
  Horizontal.cyclesRepresentation_isSmooth H σ τb hσ hτb hιb Ab hAb sb q

/-- Smoothness of the original algebraic cycle quotient. -/
abbrev tensorAlgebraicHorizontalCohomologyFiniteRepresentation_isSmooth (q : ℕ) :=
  Horizontal.cohomologyRepresentation_isSmooth H σ τb hσ hτb hιb Ab hAb sb q

local instance coefficientHeckeAnalyticCochainGroup (q : ℕ) :
    AddCommGroup (S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] AnalyticSpace e ρ)) _

local instance coefficientHeckeAlgebraicCochainGroup (q : ℕ) :
    AddCommGroup (S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] Space e ρ)) _

local instance coefficientHeckeAnalyticCycleGroup (q : ℕ) :
    AddCommGroup (tensorAnalyticHorizontalCycles e ρ S q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) _

local instance coefficientHeckeAlgebraicCycleGroup (q : ℕ) :
    AddCommGroup (tensorAlgebraicHorizontalCycles e ρ S q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) _

section Hecke

variable [MeasurableSpace (FiniteAdelicGL F n)] [BorelSpace (FiniteAdelicGL F n)]
variable (μ : Measure (FiniteAdelicGL F n)) [μ.IsHaarMeasure]

/-- Integrate the original finite action on analytic coefficient cochains. -/
def tensorAnalyticHorizontalHeckeAction (q : ℕ) :=
  S.tensorHorizontalHeckeAction μ (analyticCompactRepresentation e ρ) q

/-- Integrate the original finite action on algebraic coefficient cochains. -/
def tensorAlgebraicHorizontalHeckeAction (q : ℕ) :=
  S.tensorHorizontalHeckeAction μ (compactRepresentation e ρ) q

/-- Integrate the original finite action on analytic differential kernels. -/
def tensorAnalyticHorizontalCyclesHeckeAction (q : ℕ) :=
  Horizontal.cyclesHeckeAction H σ τa hσ hτa hιa Aa hAa sa μ q

/-- Integrate the original finite action on the analytic cycle quotient. -/
def tensorAnalyticHorizontalCohomologyHeckeAction (q : ℕ) :=
  Horizontal.cohomologyHeckeAction H σ τa hσ hτa hιa Aa hAa sa μ q

/-- Integrate the original finite action on algebraic differential kernels. -/
def tensorAlgebraicHorizontalCyclesHeckeAction (q : ℕ) :=
  Horizontal.cyclesHeckeAction H σ τb hσ hτb hιb Ab hAb sb μ q

/-- Integrate the original finite action on the algebraic cycle quotient. -/
def tensorAlgebraicHorizontalCohomologyHeckeAction (q : ℕ) :=
  Horizontal.cohomologyHeckeAction H σ τb hσ hτb hιb Ab hAb sb μ q

/-- The analytic differential commutes with the same integrated action. -/
abbrev tensorAnalyticHorizontalDifferential_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :=
  Horizontal.differential_heckeAction H σ τa hσ hτa hιa Aa hAa sa μ q h f

/-- The analytic cycle inclusion commutes with integration. -/
abbrev tensorAnalyticHorizontalCyclesInclusion_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.cyclesInclusion_heckeAction H σ τa hσ hτa hιa Aa hAa sa μ q h f

/-- The analytic class projection commutes with integration. -/
abbrev tensorAnalyticHorizontalClass_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.cohomologyClass_heckeAction H σ τa hσ hτa hιa Aa hAa sa μ q h f

/-- The algebraic differential commutes with the same integrated action. -/
abbrev tensorAlgebraicHorizontalDifferential_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ)
    (f : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :=
  Horizontal.differential_heckeAction H σ τb hσ hτb hιb Ab hAb sb μ q h f

/-- The algebraic cycle inclusion commutes with integration. -/
abbrev tensorAlgebraicHorizontalCyclesInclusion_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.cyclesInclusion_heckeAction H σ τb hσ hτb hιb Ab hAb sb μ q h f

/-- The algebraic class projection commutes with integration. -/
abbrev tensorAlgebraicHorizontalClass_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.cohomologyClass_heckeAction H σ τb hσ hτb hιb Ab hAb sb μ q h f

/-- The original coefficient comparison commutes with integrated cochain translation. -/
abbrev tensorAnalyticAlgebraicHorizontalEquiv_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :=
  Hecke.integratedAction_intertwiner μ (sa q) (sb q)
    (tensorAnalyticAlgebraicHorizontalEquiv e ρ S q).toIntertwiningMap h f

/-- The original comparison on closed cochains commutes with integration. -/
abbrev tensorAnalyticAlgebraicHorizontalCyclesEquiv_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Hecke.integratedAction_intertwiner μ
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticAlgebraicHorizontalCyclesEquiv e ρ S q).toIntertwiningMap h f

set_option maxHeartbeats 100000 in
/-- The original comparison on cycle quotients commutes with integration. -/
abbrev tensorAnalyticAlgebraicHorizontalCohomologyEquiv_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : TensorAnalyticHorizontalCohomology e ρ S q) :=
  Horizontal.equivCohomology_heckeAction H σ τa τb hσ hτa hτb hιa hιb
    Aa Ab hAa hAb (tensorAnalyticAlgebraicHorizontalEquiv e ρ S)
    (tensorAnalyticAlgebraicHorizontalDifferential e ρ S) sa sb μ q h f

end Hecke
end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
