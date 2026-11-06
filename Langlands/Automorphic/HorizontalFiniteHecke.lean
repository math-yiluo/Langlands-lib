import Langlands.Automorphic.HorizontalCohomologyFinite
import Langlands.Automorphic.TensorHorizontal
import Langlands.Representation.AlternatingCoefficients
import Langlands.Representation.Tensor.OneFactor
import Langlands.Cohomology.Lie.HorizontalCohomologyHecke
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Smoothness and Hecke actions on actual horizontal spaces -/

noncomputable section

universe u v

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL MeasureTheory
open Langlands.Cohomology.Lie

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance horizontalHeckeRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalHeckeContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalHeckeSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalHeckeFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalHeckeStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

local instance horizontalHeckeRealLieFinite :
    FiniteDimensional ℝ (RealLieAlgebra F n) := by
  change FiniteDimensional ℝ (ArchimedeanMatrix F n)
  infer_instance

local instance horizontalHeckeReducedComplexFinite :
    FiniteDimensional ℂ (ReducedComplexLieAlgebra F n) := by
  unfold ReducedComplexLieAlgebra
  infer_instance

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance horizontalHeckeSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance horizontalHeckeCochainGroup (q : ℕ) :
    AddCommGroup (horizontalEquivariantSubmodule F n S.compactRepresentation q) :=
  Submodule.addCommGroup (horizontalEquivariantSubmodule F n S.compactRepresentation q)

/-- The existing horizontal cochains embed equivariantly in actual alternating maps. -/
def horizontalAlternatingInclusion (q : ℕ) :
    (S.horizontalFiniteRepresentation q).IntertwiningMap
      (AlternatingCoefficients.action (M := ReducedComplexLieAlgebra F n)
        S.finiteRepresentation q) where
  toLinearMap := (horizontalEquivariantSubmodule F n S.compactRepresentation q).subtype
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

/-- Finite translation on horizontal cochains is smooth in every natural degree. -/
theorem horizontalFiniteRepresentation_isSmooth (q : ℕ) :
    Langlands.IsSmooth (S.horizontalFiniteRepresentation q) :=
  Langlands.isSmooth_of_injective (S.horizontalAlternatingInclusion q)
    Subtype.val_injective
    (AlternatingCoefficients.isSmooth S.finiteRepresentation_isSmooth q)

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

local instance horizontalHeckeTensorCochainGroup
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    AddCommGroup (S.tensorHorizontalSubmodule τ q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ] (TensorProduct ℂ S.Space V))
    (S.tensorHorizontalSubmodule τ q)

/-- Finite translation remains smooth after tensoring with arbitrary coefficient vectors. -/
theorem tensorFiniteRepresentation_isSmooth :
    Langlands.IsSmooth (S.tensorFiniteRepresentation V) :=
  BinaryTensor.isSmooth_firstFactor S.finiteRepresentation_isSmooth

/-- The existing tensor horizontal cochains embed in the actual alternating-map action. -/
def tensorHorizontalAlternatingInclusion
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    (S.tensorHorizontalFiniteRepresentation τ q).IntertwiningMap
      (AlternatingCoefficients.action (M := ReducedComplexLieAlgebra F n)
        (S.tensorFiniteRepresentation V) q) where
  toLinearMap := (S.tensorHorizontalSubmodule τ q).subtype
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

/-- No finite-dimensionality premise on the coefficient space is needed. -/
theorem tensorHorizontalFiniteRepresentation_isSmooth
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    Langlands.IsSmooth (S.tensorHorizontalFiniteRepresentation τ q) :=
  Langlands.isSmooth_of_injective (S.tensorHorizontalAlternatingInclusion τ q)
    Subtype.val_injective
    (AlternatingCoefficients.isSmooth S.tensorFiniteRepresentation_isSmooth q)

section Hecke

variable [MeasurableSpace (FiniteAdelicGL F n)] [BorelSpace (FiniteAdelicGL F n)]
variable (μ : Measure (FiniteAdelicGL F n)) [μ.IsHaarMeasure]

/-- The existing nonunital finite Hecke algebra acts on actual horizontal cochains. -/
def horizontalHeckeAction (q : ℕ) :
    Hecke.HeckeAlgebra μ →ₙₐ[ℂ]
      Module.End ℂ (horizontalEquivariantSubmodule F n S.compactRepresentation q) :=
  Hecke.heckeAction μ (S.horizontalFiniteRepresentation q)
    (S.horizontalFiniteRepresentation_isSmooth q)

/-- The same integration on tensor horizontal cochains with arbitrary compact coefficients. -/
def tensorHorizontalHeckeAction
    (τ : Representation ℂ (standardInfiniteCompact F n) V) (q : ℕ) :
    Hecke.HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (S.tensorHorizontalSubmodule τ q) :=
  Hecke.heckeAction μ (S.tensorHorizontalFiniteRepresentation τ q)
    (S.tensorHorizontalFiniteRepresentation_isSmooth τ q)

section Cohomology

variable [NeZero n]

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "ρ" => S.compactRepresentation
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hρ" => S.compactRepresentation_reducedLieAction
local notation "hι" => S.horizontalCochain_infinitesimal
local notation "A" => S.horizontalFiniteRepresentation
local notation "hA" => S.horizontalDifferential_finite
local notation "hSmooth" => S.horizontalFiniteRepresentation_isSmooth

/-- Inclusion of the original closed horizontal cochains, equivariant for finite translation. -/
abbrev horizontalCyclesFiniteInclusion (q : ℕ) :=
  Horizontal.cyclesActionInclusion H σ ρ hσ hρ hι A hA q

/-- Smoothness on the actual differential kernel follows by its subtype inclusion. -/
abbrev horizontalCyclesFiniteRepresentation_isSmooth (q : ℕ) :=
  Horizontal.cyclesRepresentation_isSmooth H σ ρ hσ hρ hι A hA hSmooth q

/-- Smoothness descends through the original quotient projection. -/
abbrev horizontalCohomologyFiniteRepresentation_isSmooth (q : ℕ) :=
  Horizontal.cohomologyRepresentation_isSmooth H σ ρ hσ hρ hι A hA hSmooth q

/-- Integration on the actual closed horizontal cochains. -/
def horizontalCyclesHeckeAction (q : ℕ) :=
  Horizontal.cyclesHeckeAction H σ ρ hσ hρ hι A hA hSmooth μ q

/-- Integration on the actual quotient by differential-image boundaries. -/
def horizontalCohomologyHeckeAction (q : ℕ) :=
  Horizontal.cohomologyHeckeAction H σ ρ hσ hρ hι A hA hSmooth μ q

/-- The original differential commutes with the integrated finite translation. -/
abbrev horizontalDifferential_heckeAction (q : ℕ) (h : Hecke.HeckeAlgebra μ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :=
  Horizontal.differential_heckeAction H σ ρ hσ hρ hι A hA hSmooth μ q h f

/-- The original cycle inclusion commutes with the same integrated operators. -/
abbrev horizontalCyclesFiniteInclusion_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : S.horizontalCycles q) :=
  Horizontal.cyclesInclusion_heckeAction H σ ρ hσ hρ hι A hA hSmooth μ q h f

/-- The original class projection commutes with the integrated finite translation. -/
abbrev horizontalCohomologyClass_heckeAction (q : ℕ)
    (h : Hecke.HeckeAlgebra μ) (f : S.horizontalCycles q) :=
  Horizontal.cohomologyClass_heckeAction H σ ρ hσ hρ hι A hA hSmooth μ q h f

end Cohomology
end Hecke
end OperatorRealization
end Langlands.Automorphic
