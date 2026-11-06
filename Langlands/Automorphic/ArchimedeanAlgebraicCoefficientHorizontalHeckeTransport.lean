import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientHorizontalHecke
import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientHorizontalTransport
import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticHorizontalTransport
import Langlands.Cohomology.Lie.HorizontalCohomologyHeckeTransport

/-! # Original full automorphic transport for the finite Hecke actions -/

noncomputable section

universe uF

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

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

local instance coefficientHeckeTransportRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance coefficientHeckeTransportContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientHeckeTransportSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientHeckeTransportFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance coefficientHeckeTransportStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable {S T U : OperatorRealization F n}

local instance coefficientHeckeTransportSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable [NeZero n]
variable [MeasurableSpace (FiniteAdelicGL F n)] [BorelSpace (FiniteAdelicGL F n)]
variable (μ : MeasureTheory.Measure (FiniteAdelicGL F n)) [μ.IsHaarMeasure]

local instance coefficientHeckeTransportAnalyticCochainGroup (S : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] AnalyticSpace e ρ)) _

local instance coefficientHeckeTransportAlgebraicCochainGroup (S : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ]
      (S.Space ⊗[ℂ] Space e ρ)) _

local instance coefficientHeckeTransportAnalyticCycleGroup (S : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (tensorAnalyticHorizontalCycles e ρ S q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) _

local instance coefficientHeckeTransportAlgebraicCycleGroup (S : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (tensorAlgebraicHorizontalCycles e ρ S q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) _

/-- Integrate the original analytic cochain transport without changing its map. -/
def tensorAnalyticHorizontalHeckeMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (tensorAnalyticHorizontalMap e ρ L q)

/-- The bundled Hecke map retains the original underlying linear map. -/
abbrev tensorAnalyticHorizontalHeckeMap_toLinearMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_toLinearMap μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (tensorAnalyticHorizontalMap e ρ L q)

/-- Integrate the original analytic cycles transport without changing its map. -/
def tensorAnalyticHorizontalCyclesHeckeMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner μ
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAnalyticHorizontalCyclesMap e ρ L q)

/-- The bundled Hecke map retains the original underlying linear map. -/
abbrev tensorAnalyticHorizontalCyclesHeckeMap_toLinearMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_toLinearMap μ
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAnalyticHorizontalCyclesMap e ρ L q)

/-- Integrate the original analytic cohomology transport without changing its map. -/
def tensorAnalyticHorizontalCohomologyHeckeMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner μ
    (tensorAnalyticHorizontalCohomologyFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCohomologyFiniteRepresentation_isSmooth e ρ T q)
    (tensorAnalyticHorizontalCohomologyMap e ρ L q)

/-- The bundled Hecke map retains the original underlying linear map. -/
abbrev tensorAnalyticHorizontalCohomologyHeckeMap_toLinearMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_toLinearMap μ
    (tensorAnalyticHorizontalCohomologyFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCohomologyFiniteRepresentation_isSmooth e ρ T q)
    (tensorAnalyticHorizontalCohomologyMap e ρ L q)

/-- Integrate the original algebraic cochain transport without changing its map. -/
def tensorAlgebraicHorizontalHeckeMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (tensorAlgebraicHorizontalMap e ρ L q)

/-- The bundled Hecke map retains the original underlying linear map. -/
abbrev tensorAlgebraicHorizontalHeckeMap_toLinearMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_toLinearMap μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (tensorAlgebraicHorizontalMap e ρ L q)

/-- Integrate the original algebraic cycles transport without changing its map. -/
def tensorAlgebraicHorizontalCyclesHeckeMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner μ
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAlgebraicHorizontalCyclesMap e ρ L q)

/-- The bundled Hecke map retains the original underlying linear map. -/
abbrev tensorAlgebraicHorizontalCyclesHeckeMap_toLinearMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_toLinearMap μ
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAlgebraicHorizontalCyclesMap e ρ L q)

/-- Integrate the original algebraic cohomology transport without changing its map. -/
def tensorAlgebraicHorizontalCohomologyHeckeMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner μ
    (tensorAlgebraicHorizontalCohomologyFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCohomologyFiniteRepresentation_isSmooth e ρ T q)
    (tensorAlgebraicHorizontalCohomologyMap e ρ L q)

/-- The bundled Hecke map retains the original underlying linear map. -/
abbrev tensorAlgebraicHorizontalCohomologyHeckeMap_toLinearMap (L : S.Intertwiner T) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_toLinearMap μ
    (tensorAlgebraicHorizontalCohomologyFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCohomologyFiniteRepresentation_isSmooth e ρ T q)
    (tensorAlgebraicHorizontalCohomologyMap e ρ L q)

/-- The original identity law passes to the integrated transport. -/
abbrev tensorAnalyticHorizontalHeckeMap_id (S : OperatorRealization F n) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_id_of_eq μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (tensorAnalyticHorizontalMap e ρ (Representation.IntertwiningMap.id S.representation) q)
    (tensorAnalyticHorizontalMap_id e ρ S q)

/-- The original composition law passes to the integrated transport. -/
abbrev tensorAnalyticHorizontalHeckeMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_comp_of_eq μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (U.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (tensorAnalyticHorizontalMap e ρ L q) (tensorAnalyticHorizontalMap e ρ M q)
    (tensorAnalyticHorizontalMap e ρ (M.comp L) q)
    (tensorAnalyticHorizontalMap_comp e ρ L M q)

/-- The original identity law passes to the integrated transport. -/
abbrev tensorAnalyticHorizontalCyclesHeckeMap_id (S : OperatorRealization F n) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_id_of_eq μ
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCyclesMap e ρ (Representation.IntertwiningMap.id S.representation) q)
    (tensorAnalyticHorizontalCyclesMap_id e ρ S q)

set_option maxHeartbeats 100000 in
/-- The original composition law passes to the integrated transport. -/
abbrev tensorAnalyticHorizontalCyclesHeckeMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_comp_of_eq μ
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ U q)
    (tensorAnalyticHorizontalCyclesMap e ρ L q) (tensorAnalyticHorizontalCyclesMap e ρ M q)
    (tensorAnalyticHorizontalCyclesMap e ρ (M.comp L) q)
    (tensorAnalyticHorizontalCyclesMap_comp e ρ L M q)

/-- The original cochain identity law passes to the integrated quotient map. -/
abbrev tensorAnalyticHorizontalCohomologyHeckeMap_id (S : OperatorRealization F n) (q : ℕ) :=
  Horizontal.mapCohomologyHeckeIntertwiner_id_of_eq
    (H := compactInReducedSubmodule F n) (σ := reducedCompactRepresentation F n)
    (ρ := S.tensorCompactRepresentation (analyticCompactRepresentation e ρ))
    (hσ := fun k X Y => LieEquiv.map_lie
      (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
    (hρ := tensorAnalyticCompactRepresentation_reduced_lie e ρ S)
    (hι := tensorAnalyticHorizontal_infinitesimal e ρ S)
    (actionM := S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (hActionM := tensorAnalyticHorizontalDifferential_finite e ρ S)
    (hSmoothM := S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ))
    (μ := μ)
    (tensorAnalyticHorizontalMap e ρ (Representation.IntertwiningMap.id S.representation))
    (tensorAnalyticHorizontalMap_differential e ρ
      (Representation.IntertwiningMap.id S.representation))
    (tensorAnalyticHorizontalMap_id e ρ S) q

set_option maxHeartbeats 100000 in
/-- The original cochain composition law passes to the integrated quotient maps. -/
abbrev tensorAnalyticHorizontalCohomologyHeckeMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Horizontal.mapCohomologyHeckeIntertwiner_comp_of_eq
    (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
    (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ))
    (T.tensorCompactRepresentation (analyticCompactRepresentation e ρ))
    (fun k X Y => LieEquiv.map_lie
      (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
    (tensorAnalyticCompactRepresentation_reduced_lie e ρ S)
    (tensorAnalyticCompactRepresentation_reduced_lie e ρ T)
    (tensorAnalyticHorizontal_infinitesimal e ρ S)
    (tensorAnalyticHorizontal_infinitesimal e ρ T)
    (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (tensorAnalyticHorizontalDifferential_finite e ρ S)
    (tensorAnalyticHorizontalDifferential_finite e ρ T)
    (tensorAnalyticHorizontalMap e ρ L) (tensorAnalyticHorizontalMap_differential e ρ L)
    (S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ)) μ
    (U.tensorCompactRepresentation (analyticCompactRepresentation e ρ))
    (tensorAnalyticCompactRepresentation_reduced_lie e ρ U)
    (tensorAnalyticHorizontal_infinitesimal e ρ U)
    (U.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (tensorAnalyticHorizontalDifferential_finite e ρ U)
    (tensorAnalyticHorizontalMap e ρ M) (tensorAnalyticHorizontalMap_differential e ρ M)
    (tensorAnalyticHorizontalMap e ρ (M.comp L))
    (tensorAnalyticHorizontalMap_differential e ρ (M.comp L))
    (tensorAnalyticHorizontalMap_comp e ρ L M)
    (U.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ)) q

/-- The original identity law passes to the integrated transport. -/
abbrev tensorAlgebraicHorizontalHeckeMap_id (S : OperatorRealization F n) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_id_of_eq μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (tensorAlgebraicHorizontalMap e ρ (Representation.IntertwiningMap.id S.representation) q)
    (tensorAlgebraicHorizontalMap_id e ρ S q)

/-- The original composition law passes to the integrated transport. -/
abbrev tensorAlgebraicHorizontalHeckeMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_comp_of_eq μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (U.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (tensorAlgebraicHorizontalMap e ρ L q) (tensorAlgebraicHorizontalMap e ρ M q)
    (tensorAlgebraicHorizontalMap e ρ (M.comp L) q)
    (tensorAlgebraicHorizontalMap_comp e ρ L M q)

/-- The original identity law passes to the integrated transport. -/
abbrev tensorAlgebraicHorizontalCyclesHeckeMap_id (S : OperatorRealization F n) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_id_of_eq μ
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCyclesMap e ρ (Representation.IntertwiningMap.id S.representation) q)
    (tensorAlgebraicHorizontalCyclesMap_id e ρ S q)

set_option maxHeartbeats 100000 in
/-- The original composition law passes to the integrated transport. -/
abbrev tensorAlgebraicHorizontalCyclesHeckeMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Hecke.heckeActionIntertwiner_comp_of_eq μ
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ U q)
    (tensorAlgebraicHorizontalCyclesMap e ρ L q) (tensorAlgebraicHorizontalCyclesMap e ρ M q)
    (tensorAlgebraicHorizontalCyclesMap e ρ (M.comp L) q)
    (tensorAlgebraicHorizontalCyclesMap_comp e ρ L M q)

/-- The original cochain identity law passes to the integrated quotient map. -/
abbrev tensorAlgebraicHorizontalCohomologyHeckeMap_id (S : OperatorRealization F n) (q : ℕ) :=
  Horizontal.mapCohomologyHeckeIntertwiner_id_of_eq
    (H := compactInReducedSubmodule F n) (σ := reducedCompactRepresentation F n)
    (ρ := S.tensorCompactRepresentation (compactRepresentation e ρ))
    (hσ := fun k X Y => LieEquiv.map_lie
      (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
    (hρ := tensorAlgebraicCompactRepresentation_reduced_lie e ρ S)
    (hι := tensorAlgebraicHorizontal_infinitesimal e ρ S)
    (actionM := S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (hActionM := tensorAlgebraicHorizontalDifferential_finite e ρ S)
    (hSmoothM := S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ))
    (μ := μ)
    (tensorAlgebraicHorizontalMap e ρ (Representation.IntertwiningMap.id S.representation))
    (tensorAlgebraicHorizontalMap_differential e ρ
      (Representation.IntertwiningMap.id S.representation))
    (tensorAlgebraicHorizontalMap_id e ρ S) q

set_option maxHeartbeats 100000 in
/-- The original cochain composition law passes to the integrated quotient maps. -/
abbrev tensorAlgebraicHorizontalCohomologyHeckeMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Horizontal.mapCohomologyHeckeIntertwiner_comp_of_eq
    (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
    (S.tensorCompactRepresentation (compactRepresentation e ρ))
    (T.tensorCompactRepresentation (compactRepresentation e ρ))
    (fun k X Y => LieEquiv.map_lie
      (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
    (tensorAlgebraicCompactRepresentation_reduced_lie e ρ S)
    (tensorAlgebraicCompactRepresentation_reduced_lie e ρ T)
    (tensorAlgebraicHorizontal_infinitesimal e ρ S)
    (tensorAlgebraicHorizontal_infinitesimal e ρ T)
    (S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (tensorAlgebraicHorizontalDifferential_finite e ρ S)
    (tensorAlgebraicHorizontalDifferential_finite e ρ T)
    (tensorAlgebraicHorizontalMap e ρ L) (tensorAlgebraicHorizontalMap_differential e ρ L)
    (S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ)) μ
    (U.tensorCompactRepresentation (compactRepresentation e ρ))
    (tensorAlgebraicCompactRepresentation_reduced_lie e ρ U)
    (tensorAlgebraicHorizontal_infinitesimal e ρ U)
    (U.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (tensorAlgebraicHorizontalDifferential_finite e ρ U)
    (tensorAlgebraicHorizontalMap e ρ M) (tensorAlgebraicHorizontalMap_differential e ρ M)
    (tensorAlgebraicHorizontalMap e ρ (M.comp L))
    (tensorAlgebraicHorizontalMap_differential e ρ (M.comp L))
    (tensorAlgebraicHorizontalMap_comp e ρ L M)
    (U.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ)) q

/-- The integrated map evaluates to the original transported element. -/
abbrev tensorAnalyticHorizontalHeckeMap_apply (L : S.Intertwiner T) (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :=
  Hecke.heckeActionIntertwiner_apply μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ) q)
    (tensorAnalyticHorizontalMap e ρ L q) f

/-- The integrated map evaluates to the original transported element. -/
abbrev tensorAnalyticHorizontalCyclesHeckeMap_apply (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Hecke.heckeActionIntertwiner_apply μ
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAnalyticHorizontalCyclesMap e ρ L q) f

/-- The integrated map evaluates to the original transported element. -/
abbrev tensorAnalyticHorizontalCohomologyHeckeMap_apply (L : S.Intertwiner T) (q : ℕ)
    (f : TensorAnalyticHorizontalCohomology e ρ S q) :=
  Hecke.heckeActionIntertwiner_apply μ
    (tensorAnalyticHorizontalCohomologyFiniteRepresentation_isSmooth e ρ S q)
    (tensorAnalyticHorizontalCohomologyFiniteRepresentation_isSmooth e ρ T q)
    (tensorAnalyticHorizontalCohomologyMap e ρ L q) f

set_option maxHeartbeats 100000 in
/-- The integrated quotient map sends a cycle class to its transported class. -/
abbrev tensorAnalyticHorizontalCohomologyHeckeMap_class (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.mapCohomologyHeckeIntertwiner_class
    (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
    (S.tensorCompactRepresentation (analyticCompactRepresentation e ρ))
    (T.tensorCompactRepresentation (analyticCompactRepresentation e ρ))
    (fun k X Y => LieEquiv.map_lie
      (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
    (tensorAnalyticCompactRepresentation_reduced_lie e ρ S)
    (tensorAnalyticCompactRepresentation_reduced_lie e ρ T)
    (tensorAnalyticHorizontal_infinitesimal e ρ S)
    (tensorAnalyticHorizontal_infinitesimal e ρ T)
    (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (tensorAnalyticHorizontalDifferential_finite e ρ S)
    (tensorAnalyticHorizontalDifferential_finite e ρ T)
    (tensorAnalyticHorizontalMap e ρ L) (tensorAnalyticHorizontalMap_differential e ρ L)
    (S.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation_isSmooth (analyticCompactRepresentation e ρ)) μ q f

/-- The integrated map evaluates to the original transported element. -/
abbrev tensorAlgebraicHorizontalHeckeMap_apply (L : S.Intertwiner T) (q : ℕ)
    (f : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :=
  Hecke.heckeActionIntertwiner_apply μ
    (S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (T.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ) q)
    (tensorAlgebraicHorizontalMap e ρ L q) f

/-- The integrated map evaluates to the original transported element. -/
abbrev tensorAlgebraicHorizontalCyclesHeckeMap_apply (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Hecke.heckeActionIntertwiner_apply μ
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation_isSmooth e ρ T q)
    (tensorAlgebraicHorizontalCyclesMap e ρ L q) f

/-- The integrated map evaluates to the original transported element. -/
abbrev tensorAlgebraicHorizontalCohomologyHeckeMap_apply (L : S.Intertwiner T) (q : ℕ)
    (f : TensorAlgebraicHorizontalCohomology e ρ S q) :=
  Hecke.heckeActionIntertwiner_apply μ
    (tensorAlgebraicHorizontalCohomologyFiniteRepresentation_isSmooth e ρ S q)
    (tensorAlgebraicHorizontalCohomologyFiniteRepresentation_isSmooth e ρ T q)
    (tensorAlgebraicHorizontalCohomologyMap e ρ L q) f

set_option maxHeartbeats 100000 in
/-- The integrated quotient map sends a cycle class to its transported class. -/
abbrev tensorAlgebraicHorizontalCohomologyHeckeMap_class (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.mapCohomologyHeckeIntertwiner_class
    (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
    (S.tensorCompactRepresentation (compactRepresentation e ρ))
    (T.tensorCompactRepresentation (compactRepresentation e ρ))
    (fun k X Y => LieEquiv.map_lie
      (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
    (tensorAlgebraicCompactRepresentation_reduced_lie e ρ S)
    (tensorAlgebraicCompactRepresentation_reduced_lie e ρ T)
    (tensorAlgebraicHorizontal_infinitesimal e ρ S)
    (tensorAlgebraicHorizontal_infinitesimal e ρ T)
    (S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (tensorAlgebraicHorizontalDifferential_finite e ρ S)
    (tensorAlgebraicHorizontalDifferential_finite e ρ T)
    (tensorAlgebraicHorizontalMap e ρ L) (tensorAlgebraicHorizontalMap_differential e ρ L)
    (S.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ))
    (T.tensorHorizontalFiniteRepresentation_isSmooth (compactRepresentation e ρ)) μ q f

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
