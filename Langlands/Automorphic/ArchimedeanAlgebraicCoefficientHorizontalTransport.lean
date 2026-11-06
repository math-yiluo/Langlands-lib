import Langlands.Automorphic.ArchimedeanAlgebraicCoefficientHorizontalComparison
import Langlands.Cohomology.Lie.HorizontalCohomologyIntertwinerLaws

/-! # Full automorphic maps on actual algebraic coefficient cohomology -/

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

local instance coefficientTransportRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance coefficientTransportContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientTransportSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance coefficientTransportFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance coefficientTransportStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable {S T U : OperatorRealization F n}

local instance coefficientTransportSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The original tensor map, restricted to the actual reduced algebra. -/
def tensorAlgebraicIntertwinerReducedLieHom (L : S.Intertwiner T) :
    (S.Space ⊗[ℂ] Space e ρ) →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆
      (T.Space ⊗[ℂ] Space e ρ) where
  toLinearMap := (OperatorRealization.tensorCompactMap L
    (Representation.IntertwiningMap.id (compactRepresentation e ρ))).toLinearMap
  map_lie' := fun {X v} =>
    (OperatorRealization.tensorComplexLieMap L
      (LieModuleHom.id : (Space e ρ) →ₗ⁅ℂ, ComplexLieAlgebra F n⁆ (Space e ρ))).map_lie
        (reducedComplexInclusion F n X) v

@[simp]
theorem tensorAlgebraicIntertwinerReducedLieHom_tmul (L : S.Intertwiner T)
    (f : S.Space) (v : Space e ρ) :
    tensorAlgebraicIntertwinerReducedLieHom e ρ L (f ⊗ₜ[ℂ] v) =
      L f ⊗ₜ[ℂ] v := rfl

/-- The original full operator map acts on the automorphic factor alone. -/
def tensorAlgebraicHorizontalMap (L : S.Intertwiner T) (q : ℕ) :
    (S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ) q).IntertwiningMap
      (T.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ) q) :=
  OperatorRealization.tensorHorizontalMap q L
    (Representation.IntertwiningMap.id (compactRepresentation e ρ))

@[simp]
theorem tensorAlgebraicHorizontalMap_val (L : S.Intertwiner T) (q : ℕ)
    (f : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :
    (tensorAlgebraicHorizontalMap e ρ L q f).val =
      Langlands.Cohomology.Lie.map (tensorAlgebraicIntertwinerReducedLieHom e ρ L)
        q f.val := rfl

@[simp]
theorem tensorAlgebraicHorizontalMap_id (S : OperatorRealization F n) (q : ℕ) :
    tensorAlgebraicHorizontalMap e ρ (Representation.IntertwiningMap.id S.representation) q =
      Representation.IntertwiningMap.id
        (S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ) q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  change TensorProduct.map (LinearMap.id : S.Space →ₗ[ℂ] S.Space)
      (LinearMap.id : Space e ρ →ₗ[ℂ] Space e ρ) (f.val X) = f.val X
  exact LinearMap.congr_fun TensorProduct.map_id (f.val X)

theorem tensorAlgebraicHorizontalMap_comp (L : S.Intertwiner T) (M : T.Intertwiner U)
    (q : ℕ) :
    tensorAlgebraicHorizontalMap e ρ (M.comp L) q =
      (tensorAlgebraicHorizontalMap e ρ M q).comp
        (tensorAlgebraicHorizontalMap e ρ L q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  change TensorProduct.map (M.toLinearMap.comp L.toLinearMap)
      (LinearMap.id : Space e ρ →ₗ[ℂ] Space e ρ) (f.val X) =
    TensorProduct.map M.toLinearMap (LinearMap.id : Space e ρ →ₗ[ℂ] Space e ρ)
      (TensorProduct.map L.toLinearMap (LinearMap.id : Space e ρ →ₗ[ℂ] Space e ρ)
        (f.val X))
  exact LinearMap.congr_fun
    (by simpa only [LinearMap.id_comp] using
      (TensorProduct.map_comp M.toLinearMap (LinearMap.id : Space e ρ →ₗ[ℂ] Space e ρ)
        L.toLinearMap (LinearMap.id : Space e ρ →ₗ[ℂ] Space e ρ))) (f.val X)

variable [NeZero n]

/-- Chain compatibility follows from the original reduced tensor Lie map. -/
theorem tensorAlgebraicHorizontalMap_differential (L : S.Intertwiner T) (q : ℕ)
    (f : S.tensorHorizontalSubmodule (compactRepresentation e ρ) q) :
    tensorAlgebraicHorizontalDifferential e ρ T q (tensorAlgebraicHorizontalMap e ρ L q f) =
      tensorAlgebraicHorizontalMap e ρ L (q + 1)
        (tensorAlgebraicHorizontalDifferential e ρ S q f) := by
  apply Subtype.ext
  exact (Langlands.Cohomology.Lie.map_differential
    (tensorAlgebraicIntertwinerReducedLieHom e ρ L) q f.val).symm

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "τS" => S.tensorCompactRepresentation (compactRepresentation e ρ)
local notation "τT" => T.tensorCompactRepresentation (compactRepresentation e ρ)
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hτS" => tensorAlgebraicCompactRepresentation_reduced_lie e ρ S
local notation "hτT" => tensorAlgebraicCompactRepresentation_reduced_lie e ρ T
local notation "hιS" => tensorAlgebraicHorizontal_infinitesimal e ρ S
local notation "hιT" => tensorAlgebraicHorizontal_infinitesimal e ρ T
local notation "AS" => S.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ)
local notation "AT" => T.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ)
local notation "hAS" => tensorAlgebraicHorizontalDifferential_finite e ρ S
local notation "hAT" => tensorAlgebraicHorizontalDifferential_finite e ρ T

/-- Restrict the same original map to the actual differential kernel. -/
def tensorAlgebraicHorizontalCyclesMap (L : S.Intertwiner T) (q : ℕ) :
    (tensorAlgebraicHorizontalCyclesFiniteRepresentation e ρ S q).IntertwiningMap
      (tensorAlgebraicHorizontalCyclesFiniteRepresentation e ρ T q) :=
  Horizontal.mapCyclesIntertwiner H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAlgebraicHorizontalMap e ρ L) (tensorAlgebraicHorizontalMap_differential e ρ L) q

/-- Descend the same original map to the actual cycle quotient. -/
def tensorAlgebraicHorizontalCohomologyMap (L : S.Intertwiner T) (q : ℕ) :
    (tensorAlgebraicHorizontalCohomologyFiniteRepresentation e ρ S q).IntertwiningMap
      (tensorAlgebraicHorizontalCohomologyFiniteRepresentation e ρ T q) :=
  Horizontal.mapCohomologyIntertwiner H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAlgebraicHorizontalMap e ρ L) (tensorAlgebraicHorizontalMap_differential e ρ L) q

/-- The generic cycle formula specialized without an extra target conversion. -/
@[simp]
abbrev tensorAlgebraicHorizontalCyclesMap_val (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.mapCyclesIntertwiner_val H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAlgebraicHorizontalMap e ρ L) (tensorAlgebraicHorizontalMap_differential e ρ L) q f


/-- Transport sends a quotient class to the class of its transported cycle. -/
@[simp]
abbrev tensorAlgebraicHorizontalCohomologyMap_class (L : S.Intertwiner T) (q : ℕ)
    (f : tensorAlgebraicHorizontalCycles e ρ S q) :=
  Horizontal.mapCohomologyIntertwiner_class H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAlgebraicHorizontalMap e ρ L) (tensorAlgebraicHorizontalMap_differential e ρ L) q f

/-- The existing quotient projection is natural for full automorphic maps. -/
abbrev tensorAlgebraicHorizontalCohomologyMap_class_comp (L : S.Intertwiner T) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwiner_class_comp H σ τS τT hσ hτS hτT hιS hιT AS AT hAS hAT
    (tensorAlgebraicHorizontalMap e ρ L) (tensorAlgebraicHorizontalMap_differential e ρ L) q

@[simp]
abbrev tensorAlgebraicHorizontalCyclesMap_id (S0 : OperatorRealization F n) (q : ℕ) :=
  Horizontal.mapCyclesIntertwiner_id_of_eq H σ
    (S0.tensorCompactRepresentation (compactRepresentation e ρ)) hσ
    (tensorAlgebraicCompactRepresentation_reduced_lie e ρ S0)
    (tensorAlgebraicHorizontal_infinitesimal e ρ S0)
    (S0.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (tensorAlgebraicHorizontalDifferential_finite e ρ S0)
    (tensorAlgebraicHorizontalMap e ρ (Representation.IntertwiningMap.id S0.representation))
    (tensorAlgebraicHorizontalMap_differential e ρ
      (Representation.IntertwiningMap.id S0.representation))
    (tensorAlgebraicHorizontalMap_id e ρ S0) q

local notation "τU" => U.tensorCompactRepresentation (compactRepresentation e ρ)
local notation "hτU" => tensorAlgebraicCompactRepresentation_reduced_lie e ρ U
local notation "hιU" => tensorAlgebraicHorizontal_infinitesimal e ρ U
local notation "AU" => U.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ)
local notation "hAU" => tensorAlgebraicHorizontalDifferential_finite e ρ U

abbrev tensorAlgebraicHorizontalCyclesMap_comp
    (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Horizontal.mapCyclesIntertwiner_comp_of_eq H σ τS τT hσ hτS hτT hιS hιT
    AS AT hAS hAT (tensorAlgebraicHorizontalMap e ρ L)
    (tensorAlgebraicHorizontalMap_differential e ρ L)
    τU hτU hιU AU hAU (tensorAlgebraicHorizontalMap e ρ M)
    (tensorAlgebraicHorizontalMap_differential e ρ M)
    (tensorAlgebraicHorizontalMap e ρ (M.comp L))
    (tensorAlgebraicHorizontalMap_differential e ρ (M.comp L))
    (tensorAlgebraicHorizontalMap_comp e ρ L M) q

@[simp]
abbrev tensorAlgebraicHorizontalCohomologyMap_id (S0 : OperatorRealization F n) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwiner_id_of_eq H σ
    (S0.tensorCompactRepresentation (compactRepresentation e ρ)) hσ
    (tensorAlgebraicCompactRepresentation_reduced_lie e ρ S0)
    (tensorAlgebraicHorizontal_infinitesimal e ρ S0)
    (S0.tensorHorizontalFiniteRepresentation (compactRepresentation e ρ))
    (tensorAlgebraicHorizontalDifferential_finite e ρ S0)
    (tensorAlgebraicHorizontalMap e ρ (Representation.IntertwiningMap.id S0.representation))
    (tensorAlgebraicHorizontalMap_differential e ρ
      (Representation.IntertwiningMap.id S0.representation))
    (tensorAlgebraicHorizontalMap_id e ρ S0) q

abbrev tensorAlgebraicHorizontalCohomologyMap_comp
    (L : S.Intertwiner T) (M : T.Intertwiner U) (q : ℕ) :=
  Horizontal.mapCohomologyIntertwiner_comp_of_eq H σ τS τT hσ hτS hτT hιS hιT
    AS AT hAS hAT (tensorAlgebraicHorizontalMap e ρ L)
    (tensorAlgebraicHorizontalMap_differential e ρ L)
    τU hτU hιU AU hAU (tensorAlgebraicHorizontalMap e ρ M)
    (tensorAlgebraicHorizontalMap_differential e ρ M)
    (tensorAlgebraicHorizontalMap e ρ (M.comp L))
    (tensorAlgebraicHorizontalMap_differential e ρ (M.comp L))
    (tensorAlgebraicHorizontalMap_comp e ρ L M) q

end Langlands.Automorphic.ArchimedeanAlgebraicCoefficient
