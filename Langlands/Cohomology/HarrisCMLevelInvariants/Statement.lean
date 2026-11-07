import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology
import Langlands.Shimura.PEL.HarrisTaylorCMNormalActions

/-!
# Level invariants of CM cohomology at finite level

For sufficiently small CM levels `V ≤ U` with `V` normal in `U`, the map
`X̄_V → X̄_U` of the Library's geometric CM tower is a finite étale
`U/V`-torsor whose deck maps are the tower maps of the level arrows
`⟨g⁻¹⟩ : V ⟶ V` for `g ∈ U`. This module states the Harris–Taylor
comparison `H^d(X̄_U, F_U) ≅ H^d(X̄_V, F_V)^{U/V}` (Harris–Taylor III.2,
p.96) for level-trivial coefficient diagrams whose transition map along
`V ≤ U` is an isomorphism, when the index `[U : V]` is invertible in `R`. The
truth argument is the trace method of SGA 4 IX 5.1.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMLevelInvariants

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura Langlands.Shimura.PEL
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
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
  (q : CMRepresentabilityStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})
  (R : Type) [CommRing R]

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "towerEtale" => cmSmallLevelTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion
local notation "coefficients" => cmSmallLevelCoefficientDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "trivialCoefficients" => cmSmallLevelTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "levelCohomology" => cmSmallLevelCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- Finite-level invariants (Harris–Taylor III.2, p.96). Let `coeff` be a
level-trivial diagram of sheaves of `R`-modules on the Library's geometric CM
tower, let `V ≤ U` be sufficiently small levels with `V` normal in `U`, and
suppose that the transition map of `coeff` along the inclusion `V ≤ U`, from the
pullback of the level-`U` sheaf to the level-`V` sheaf, is an isomorphism and
that the index `[U : V]` is a unit of `R`. Then in every degree `d` the
restriction map `H^d(X̄_U, coeff_U) → H^d(X̄_V, coeff_V)` is injective, and its
image is the set of classes fixed by the maps of the tower along the arrows
`⟨g⁻¹⟩ : V ⟶ V` for all `g ∈ U`. -/
def HarrisCMLevelInvariantsStatement : Prop :=
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  ∀ (coeff : coefficients), trivialCoefficients coeff →
    ∀ (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
      [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal],
      IsIso (coeff.map (smallCMInclusion D hVU).op) →
      IsUnit ((V.obj.subgroup.subgroupOf U.obj.subgroup).index : R) →
      ∀ d : ℕ,
        Function.Injective ((levelCohomology coeff d).map (smallCMInclusion D hVU).op).hom ∧
        Set.range ((levelCohomology coeff d).map (smallCMInclusion D hVU).op).hom =
          {y | ∀ g : U.obj.subgroup,
            ((levelCohomology coeff d).map
              (smallCMNormalInverseArrow D U V hVU g).op).hom y = y}

end Langlands.Cohomology.HarrisCMLevelInvariants
