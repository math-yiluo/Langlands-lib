import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientAnalyticHorizontalFinite
import Langlands.Cohomology.Lie.HorizontalCohomologyIntertwinerLaws

/-! # Full automorphic maps on actual analytic coefficient cohomology -/

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

local instance analyticCoefficientTransportRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance analyticCoefficientTransportContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticCoefficientTransportSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance analyticCoefficientTransportFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance analyticCoefficientTransportStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable {S T U : OperatorRealization F n}

local instance analyticCoefficientTransportSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The original tensor map, restricted to the actual reduced algebra. -/
def tensorAnalyticIntertwinerReducedLieHom (L : S.Intertwiner T) :
    (S.Space ⊗[ℂ] AnalyticSpace e ρ) →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆
      (T.Space ⊗[ℂ] AnalyticSpace e ρ) where
  toLinearMap := (OperatorRealization.tensorCompactMap L
    (Representation.IntertwiningMap.id (analyticCompactRepresentation e ρ))).toLinearMap
  map_lie' := fun {X v} =>
    (OperatorRealization.tensorComplexLieMap L
      (LieModuleHom.id : (AnalyticSpace e ρ) →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ (AnalyticSpace e ρ))).map_lie
        (reducedComplexInclusion F n X) v

@[simp]
theorem tensorAnalyticIntertwinerReducedLieHom_tmul (L : S.Intertwiner T)
    (f : S.Space) (v : AnalyticSpace e ρ) :
    tensorAnalyticIntertwinerReducedLieHom e ρ L (f ⊗ₜ[ℂ] v) =
      L f ⊗ₜ[ℂ] v := rfl

/-- The original full operator map acts on the automorphic factor alone. -/
def tensorAnalyticHorizontalMap (L : S.Intertwiner T) (q : ℕ) :
    (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) q).IntertwiningMap
      (T.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) q) :=
  OperatorRealization.tensorHorizontalMap q L
    (Representation.IntertwiningMap.id (analyticCompactRepresentation e ρ))

@[simp]
theorem tensorAnalyticHorizontalMap_val (L : S.Intertwiner T) (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :
    (tensorAnalyticHorizontalMap e ρ L q f).val =
      Langlands.Cohomology.Lie.map (tensorAnalyticIntertwinerReducedLieHom e ρ L)
        q f.val := rfl

@[simp]
theorem tensorAnalyticHorizontalMap_id (S : OperatorRealization F n) (q : ℕ) :
    tensorAnalyticHorizontalMap e ρ (Representation.IntertwiningMap.id S.representation) q =
      Representation.IntertwiningMap.id
        (S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ) q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  change TensorProduct.map (LinearMap.id : S.Space →ₗ[ℂ] S.Space)
      (LinearMap.id : AnalyticSpace e ρ →ₗ[ℂ] AnalyticSpace e ρ) (f.val X) = f.val X
  exact LinearMap.congr_fun TensorProduct.map_id (f.val X)

theorem tensorAnalyticHorizontalMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U)
    (q : ℕ) :
    tensorAnalyticHorizontalMap e ρ (M.comp L) q =
      (tensorAnalyticHorizontalMap e ρ M q).comp
        (tensorAnalyticHorizontalMap e ρ L q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  change TensorProduct.map (M.toLinearMap.comp L.toLinearMap)
      (LinearMap.id : AnalyticSpace e ρ →ₗ[ℂ] AnalyticSpace e ρ) (f.val X) =
    TensorProduct.map M.toLinearMap (LinearMap.id : AnalyticSpace e ρ →ₗ[ℂ] AnalyticSpace e ρ)
      (TensorProduct.map L.toLinearMap (LinearMap.id : AnalyticSpace e ρ →ₗ[ℂ] AnalyticSpace e ρ)
        (f.val X))
  exact LinearMap.congr_fun
    (by simpa only [LinearMap.id_comp] using
      (TensorProduct.map_comp M.toLinearMap (LinearMap.id : AnalyticSpace e ρ →ₗ[ℂ] AnalyticSpace e ρ)
        L.toLinearMap (LinearMap.id : AnalyticSpace e ρ →ₗ[ℂ] AnalyticSpace e ρ))) (f.val X)

variable [NeZero n]

/-- Chain compatibility follows from the original reduced tensor Lie map. -/
theorem tensorAnalyticHorizontalMap_differential (L : S.Intertwiner T) (q : ℕ)
    (f : S.tensorHorizontalSubmodule (analyticCompactRepresentation e ρ) q) :
    tensorAnalyticHorizontalDifferential e ρ T q (tensorAnalyticHorizontalMap e ρ L q f) =
      tensorAnalyticHorizontalMap e ρ L (q + 1)
        (tensorAnalyticHorizontalDifferential e ρ S q f) := by
  apply Subtype.ext
  exact (Langlands.Cohomology.Lie.map_differential
    (tensorAnalyticIntertwinerReducedLieHom e ρ L) q f.val).symm

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "τS" => S.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "τT" => T.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hτS" => tensorAnalyticCompactRepresentation_reduced_lie e ρ S
local notation "hτT" => tensorAnalyticCompactRepresentation_reduced_lie e ρ T
local notation "hιS" => tensorAnalyticHorizontal_infinitesimal e ρ S
local notation "hιT" => tensorAnalyticHorizontal_infinitesimal e ρ T
local notation "AS" => S.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "AT" => T.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "hAS" => tensorAnalyticHorizontalDifferential_finite e ρ S
local notation "hAT" => tensorAnalyticHorizontalDifferential_finite e ρ T

/-- Restrict the same original map to the actual differential kernel. -/
def tensorAnalyticHorizontalCyclesMap (L : S.Intertwiner T) (q : ℕ) :
    (tensorAnalyticHorizontalCyclesFiniteRepresentation e ρ S q).IntertwiningMap
      (tensorAnalyticHorizontalCyclesFiniteRepresentation e ρ T q) :=
  Horizontal.mapCyclesIntertwiner H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAnalyticHorizontalMap e ρ L) (tensorAnalyticHorizontalMap_differential e ρ L) q

/-- Descend the same original map to the actual cycle quotient. -/
def tensorAnalyticHorizontalCohomologyMap (L : S.Intertwiner T) (q : ℕ) :
    (tensorAnalyticHorizontalCohomologyFiniteRepresentation e ρ S q).IntertwiningMap
      (tensorAnalyticHorizontalCohomologyFiniteRepresentation e ρ T q) :=
  Horizontal.mapCohomologyIntertwiner H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAnalyticHorizontalMap e ρ L) (tensorAnalyticHorizontalMap_differential e ρ L) q

/-- The generic cycle formula specialized without an extra target conversion. -/
@[simp]
abbrev tensorAnalyticHorizontalCyclesMap_val (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.mapCyclesIntertwiner_val H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAnalyticHorizontalMap e ρ L) (tensorAnalyticHorizontalMap_differential e ρ L) q f


/-- Transport sends a quotient class to the class of its transported cycle. -/
@[simp]
abbrev tensorAnalyticHorizontalCohomologyMap_class (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAnalyticHorizontalCycles e ρ S q) :=
  Horizontal.mapCohomologyIntertwiner_class H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAnalyticHorizontalMap e ρ L) (tensorAnalyticHorizontalMap_differential e ρ L) q f

/-- The existing quotient projection is natural for full automorphic maps. -/
abbrev tensorAnalyticHorizontalCohomologyMap_class_comp (L : S.Intertwiner T) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwiner_class_comp H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAnalyticHorizontalMap e ρ L) (tensorAnalyticHorizontalMap_differential e ρ L) q

@[simp]
abbrev tensorAnalyticHorizontalCyclesMap_id (S0 : OperatorRealization F n) (q : ℕ) :=
  Horizontal.mapCyclesIntertwiner_id_of_eq H σ
    (S0.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) hσ
    (tensorAnalyticCompactRepresentation_reduced_lie e ρ S0)
    (tensorAnalyticHorizontal_infinitesimal e ρ S0)
    (S0.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (tensorAnalyticHorizontalDifferential_finite e ρ S0)
    (tensorAnalyticHorizontalMap e ρ (Representation.IntertwiningMap.id S0.representation))
    (tensorAnalyticHorizontalMap_differential e ρ
      (Representation.IntertwiningMap.id S0.representation))
    (tensorAnalyticHorizontalMap_id e ρ S0) q

local notation "τU" => U.tensorCompactRepresentation (analyticCompactRepresentation e ρ)
local notation "hτU" => tensorAnalyticCompactRepresentation_reduced_lie e ρ U
local notation "hιU" => tensorAnalyticHorizontal_infinitesimal e ρ U
local notation "AU" => U.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ)
local notation "hAU" => tensorAnalyticHorizontalDifferential_finite e ρ U

abbrev tensorAnalyticHorizontalCyclesMap_comp
    (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Horizontal.mapCyclesIntertwiner_comp_of_eq H σ τS τT hσ hτS hτT hιS hιT
    AS AT hAS hAT (tensorAnalyticHorizontalMap e ρ L)
    (tensorAnalyticHorizontalMap_differential e ρ L)
    τU hτU hιU AU hAU (tensorAnalyticHorizontalMap e ρ M)
    (tensorAnalyticHorizontalMap_differential e ρ M)
    (tensorAnalyticHorizontalMap e ρ (M.comp L))
    (tensorAnalyticHorizontalMap_differential e ρ (M.comp L))
    (tensorAnalyticHorizontalMap_comp e ρ L M) q

@[simp]
abbrev tensorAnalyticHorizontalCohomologyMap_id (S0 : OperatorRealization F n) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwiner_id_of_eq H σ
    (S0.tensorCompactRepresentation (analyticCompactRepresentation e ρ)) hσ
    (tensorAnalyticCompactRepresentation_reduced_lie e ρ S0)
    (tensorAnalyticHorizontal_infinitesimal e ρ S0)
    (S0.tensorHorizontalFiniteRepresentation (analyticCompactRepresentation e ρ))
    (tensorAnalyticHorizontalDifferential_finite e ρ S0)
    (tensorAnalyticHorizontalMap e ρ (Representation.IntertwiningMap.id S0.representation))
    (tensorAnalyticHorizontalMap_differential e ρ
      (Representation.IntertwiningMap.id S0.representation))
    (tensorAnalyticHorizontalMap_id e ρ S0) q

abbrev tensorAnalyticHorizontalCohomologyMap_comp
    (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwiner_comp_of_eq H σ τS τT hσ hτS hτT hιS hιT
    AS AT hAS hAT (tensorAnalyticHorizontalMap e ρ L)
    (tensorAnalyticHorizontalMap_differential e ρ L)
    τU hτU hιU AU hAU (tensorAnalyticHorizontalMap e ρ M)
    (tensorAnalyticHorizontalMap_differential e ρ M)
    (tensorAnalyticHorizontalMap e ρ (M.comp L))
    (tensorAnalyticHorizontalMap_differential e ρ (M.comp L))
    (tensorAnalyticHorizontalMap_comp e ρ L M) q

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
