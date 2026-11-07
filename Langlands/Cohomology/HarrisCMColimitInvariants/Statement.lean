import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology

/-!
# Level invariants of CM cohomology over all small levels

For a `ℚ`-algebra `R` and a level-trivial diagram of sheaves of `R`-modules on
the Library's geometric CM tower whose transition maps are isomorphisms, this
module states that the cohomology `H^d(X̄_U, F_U)` at a sufficiently small
level `U` maps isomorphically onto the `U`-invariants of the colimit over all
small levels. Harris and Taylor deduce admissibility of the colimit from the
finite-level comparison of III.2, p.96; this is the step in between. The truth
argument derives it from the finite-level statement
`HarrisCMLevelInvariantsStatement`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Cohomology.HarrisCMColimitInvariants

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

/-- Invariants of the colimit over all small levels. Let `R` be a `ℚ`-algebra
and `coeff` a level-trivial diagram of sheaves of `R`-modules on the Library's
geometric CM tower all of whose transition maps are isomorphisms. Then in every
degree `d` and at every sufficiently small level `U`, the map from
`H^d(X̄_U, coeff_U)` to the colimit over all small levels is injective, and its
image is the set of classes fixed by every element of `U` under the Library's
smooth action of the finite-adelic group on that colimit. -/
def HarrisCMColimitInvariantsStatement [Algebra ℚ R] : Prop :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  ∀ (coeff : coefficients) (hcoeff : trivialCoefficients coeff),
    (∀ {i j : (SmallCMLevel D)ᵒᵖ} (a : i ⟶ j), IsIso (coeff.map a)) →
    ∀ (d : ℕ) (U : SmallCMLevel D),
      Function.Injective (RestrictedLevelColimit.ι (levelCohomology coeff d) U).hom ∧
      Set.range (RestrictedLevelColimit.ι (levelCohomology coeff d) U).hom =
        {z | ∀ u ∈ U.obj.subgroup,
          (cmSmallLevelSmoothCohomology D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor q existence geometry hRigid criterion
            R coeff hcoeff d).obj.ρ u z = z}

end Langlands.Cohomology.HarrisCMColimitInvariants
