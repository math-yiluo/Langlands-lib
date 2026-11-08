import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology
import Langlands.Shimura.DecompositionGroupAction

/-!
# Unramified Galois actions on geometric CM torsion cohomology

Fix a small CM level `U` and Worker 57's original stable-lattice torsion
coefficient system on the geometric level `X̄_U = X_U ×_{Spec F} Spec F̄`,
where `F̄ = AlgebraicClosure F`. Worker 57 constructs an action of
`F̄ ≃ₐ[F] F̄` on every étale cohomology module of every coefficient stage.
This module states that there is one finite set of finite places of `F`
outside which all these actions are unramified: the inertia subgroup of the
completion at the place acts trivially, in every degree and at every
coefficient stage. Harris uses this for the `λ`-adic representations on the
cohomology of his Shimura varieties (Harris 1999, §5). The truth argument
spreads out `X_U`, its universal abelian scheme and the coefficient covers,
and applies SGA 4 XVI Théorème 2.1 with XV 2.1.
-/

noncomputable section

universe wS wR

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMCohomologyUnramified

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

local notation "Rcoeff" => HarrisCoefficientIntegers K p

variable [HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

/-- There is a finite set `S` of finite places of `F` such that for every degree, every stage
of the original geometric CM torsion coefficient system on `X_U ×_{Spec F} Spec F̄` and every
finite place `w ∉ S`, the constructed action of `F̄ ≃ₐ[F] F̄` on the étale cohomology module is
unramified at `w`. The set `S` does not depend on the degree or the stage. -/
def HarrisCMCohomologyUnramifiedStatement : Prop :=
  ∃ S : Set (Global.FinitePlace F), S.Finite ∧
    ∀ (degree : ℕ) (r : ℕᵒᵖ) (w : Global.FinitePlace F), w ∉ S →
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{0} Rcoeff) w
        ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
          existence geometry hRigid degree).obj r)

end Langlands.Cohomology.HarrisCMCohomologyUnramified
