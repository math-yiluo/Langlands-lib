import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCohomology
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology
import Langlands.Representation.Smooth.Definitions
import Mathlib.FieldTheory.KrullTopology

/-!
# Finiteness and Galois smoothness of geometric CM torsion cohomology

Fix a small CM level `U` and Worker 57's original stable-lattice torsion
coefficient system on the geometric level `X̄_U = X_U ×_{Spec F} Spec F̄`,
where `F̄ = AlgebraicClosure F`. The first statement says that every
étale cohomology module of every coefficient stage is finite. The second says
that the constructed action of `F̄ ≃ₐ[F] F̄` on each of these modules is smooth
for the Krull topology: every class is fixed by an open subgroup. Harris uses
both facts for the cohomology of his Shimura varieties (Harris 1999, proof of
Proposition 4.10 and §5). The truth arguments use SGA 4 XIV Corollaire 1.2
and SGA 4 VII Corollaire 5.8.
-/

noncomputable section

universe wS wR

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMCohomology

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura Langlands.Shimura.PEL
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "Rcoeff" => HarrisCoefficientIntegers K p

/-- Every étale cohomology module of every stage of the original geometric
CM torsion coefficient system on `X_U ×_{Spec F} Spec F̄` is finite. -/
def HarrisCMCohomologyFiniteStatement : Prop :=
  ∀ (degree : ℕ) (r : ℕᵒᵖ),
    Finite ((cmHarrisGeometricCoefficientCohomologySystem D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid degree).obj r)

variable [HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

/-- The constructed action of `F̄ ≃ₐ[F] F̄`, with its Krull topology, on every
étale cohomology module of every stage of the original geometric CM torsion
coefficient system on `X_U ×_{Spec F} Spec F̄` is smooth. -/
def HarrisCMGaloisCohomologySmoothStatement : Prop :=
  ∀ (degree : ℕ) (r : ℕᵒᵖ),
    Langlands.IsSmooth ((Rep.ActionToRep Rcoeff Galois).obj
      ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid degree).obj r)).ρ

/-- Both statements of this module: finiteness of every geometric CM torsion
cohomology module and smoothness of the constructed Galois action on it. -/
def HarrisCMCohomologyStatements : Prop :=
  HarrisCMCohomologyFiniteStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid ∧
    HarrisCMGaloisCohomologySmoothStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

end Langlands.Cohomology.HarrisCMCohomology
