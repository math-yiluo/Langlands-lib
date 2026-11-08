import Langlands.Cohomology.HarrisCMCohomology.Statement
import Langlands.Cohomology.DivisibleSystem.ContinuousLimit
import Langlands.Shimura.LimitGaloisAction
import Langlands.Shimura.FrobeniusPolynomial

/-! # The Galois action on the `m`-power torsion limit of Harris's CM coefficient system

Fix a small CM level `U`, the original stable-lattice coefficient system of an algebraic
representation `W`, and the nonzero integer `m` of the published construction, whose stage `r`
reduces the lattice modulo the `r`-th power of the scalar ideal `(m)` of the coefficient ring
`HarrisCoefficientIntegers K p`. On the geometric level `X̄_U = X_U ×_{Spec F} Spec F̄`, the
cohomology modules of these stages in a fixed degree form an inverse system of Galois actions.
This module takes its limit in the category of Galois actions: the `m`-power torsion limit of the
cohomology, the `(m)`-adic analogue of integral `λ`-adic cohomology. No relation between `m` and
the rational place `p` is assumed; for `m = 1` every stage is zero. With the inverse limit
topology of the discrete stages the limit is Hausdorff, and the Galois action on it is jointly
continuous for the Krull topology when every stage is smooth, as in the Library statement
`HarrisCMGaloisCohomologySmoothStatement`. It is unramified at a finite place where every stage
is, its projections intertwine the geometric Frobenius endomorphisms, and when it is finite free
over the coefficient ring it has a Frobenius Euler polynomial. See
`HarrisTaylorCMAdicGaloisCohomology.md`.
-/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
open Langlands.Cohomology
open Langlands.Cohomology.HarrisCMCohomology (HarrisCMGaloisCohomologySmoothStatement)
open Langlands.GaloisRepresentation (ClosureEmbedding LocalGroup IsGeometricFrobeniusLift)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius localRestriction)

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

variable [HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]


local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "cohomologyAction" => cmHarrisGeometricGaloisCohomologyAction D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry
  hRigid

/-! ## The limit over the torsion stages -/

/-- The `m`-power torsion limit of the cohomology of the geometric CM level `X̄_U` with
coefficients in the original torsion coefficient system of `W`: the limit, in the category of
Galois actions, of the cohomology modules of degree `degree` over all stages `r`, the stage `r`
having coefficients modulo `(m)^r`. -/
def cmHarrisAdicCohomology (degree : ℕ) : Action (ModuleCat.{0} Rcoeff) Galois :=
  limit (cohomologyAction degree)

local notation "adicCohomology" => cmHarrisAdicCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry
  hRigid

/-- The projection of the torsion limit to the cohomology of the torsion stage `r`, a
morphism of Galois actions. -/
def cmHarrisAdicCohomologyπ (degree : ℕ) (r : ℕᵒᵖ) :
    adicCohomology degree ⟶ (cohomologyAction degree).obj r :=
  limit.π (cohomologyAction degree) r

/-- The torsion limit with the inverse limit topology of the discrete torsion stages. -/
abbrev CMHarrisAdicSpace (degree : ℕ) : Type :=
  ContinuousLimit.ConeSpace (limit.cone (cmHarrisGeometricGaloisCohomologyAction D C
    preservation composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid degree))

local notation "adicSpace" => CMHarrisAdicSpace D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- The torsion limit is Hausdorff. -/
instance (degree : ℕ) : T2Space (adicSpace degree) :=
  ContinuousLimit.t2Space_of_isLimit (limit.isLimit _)

/-- Under the Galois smoothness statement for every torsion stage, the action of `Gal(F̄/F)` on
the torsion limit is jointly continuous for the Krull topology. -/
theorem continuous_cmHarrisAdicAction
    (hsmooth : HarrisCMGaloisCohomologySmoothStatement.{wS, wR} D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence
      geometry hRigid)
    (degree : ℕ) :
    Continuous fun x : Galois × adicSpace degree =>
      ContinuousLimit.act (limit.cone (cohomologyAction degree)) x.1 x.2 :=
  ContinuousLimit.continuous_action _ (hsmooth degree)

/-- The Galois representation on the torsion limit by continuous linear maps. -/
abbrev cmHarrisAdicContRepresentation (degree : ℕ) :
    ContRepresentation Rcoeff Galois (adicSpace degree) :=
  ContinuousLimit.contRepresentation _

/-- For a topology on the coefficient ring acting continuously, and under the Galois smoothness
statement, the torsion limit with its jointly continuous Galois action. -/
def cmHarrisAdicContAction [TopologicalSpace Rcoeff] (degree : ℕ)
    [ContinuousSMul Rcoeff (adicSpace degree)]
    (hsmooth : HarrisCMGaloisCohomologySmoothStatement.{wS, wR} D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence
      geometry hRigid) :
    ContAction (TopModuleCat.{0} Rcoeff) Galois :=
  ContinuousLimit.contAction (limit.cone (cohomologyAction degree)) (hsmooth degree)

/-! ## Decomposition groups and Frobenius -/

section Frobenius

variable (w : Global.FinitePlace F) (degree : ℕ)

variable {w} in
/-- If every torsion stage is unramified at `w` along `j`, so is the torsion limit. -/
theorem cmHarrisAdicCohomology_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : ∀ r, IsUnramifiedAlong (ModuleCat.{0} Rcoeff) w ((cohomologyAction degree).obj r) j) :
    IsUnramifiedAlong (ModuleCat.{0} Rcoeff) w (adicCohomology degree) j :=
  LimitGaloisAction.isUnramifiedAlong_limit (K := F) hu

variable {w} in
/-- If every torsion stage is unramified at `w`, so is the torsion limit. -/
theorem cmHarrisAdicCohomology_isUnramifiedAt
    (hu : ∀ r, IsUnramifiedAt (ModuleCat.{0} Rcoeff) w ((cohomologyAction degree).obj r)) :
    IsUnramifiedAt (ModuleCat.{0} Rcoeff) w (adicCohomology degree) :=
  LimitGaloisAction.isUnramifiedAt_limit (K := F) hu

/-- The projections to the torsion stages intertwine the geometric Frobenius endomorphisms at
`w` along `j`. -/
theorem cmHarrisAdicCohomology_geometricFrobenius_π
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) (r : ℕᵒᵖ) :
    geometricFrobenius (ModuleCat.{0} Rcoeff) w (adicCohomology degree) j ≫
        (cmHarrisAdicCohomologyπ D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
          degree r).hom =
      (cmHarrisAdicCohomologyπ D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
          degree r).hom ≫
        geometricFrobenius (ModuleCat.{0} Rcoeff) w ((cohomologyAction degree).obj r) j :=
  LimitGaloisAction.geometricFrobenius_limit_π (K := F) w _ j r

variable [Module.Free (HarrisCoefficientIntegers K p)
    (cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U ρ p m hm existence geometry hRigid degree).V]
  [Module.Finite (HarrisCoefficientIntegers K p)
    (cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U ρ p m hm existence geometry hRigid degree).V]

/-- When the torsion limit is finite free over the coefficient ring, its Frobenius Euler
polynomial `det(1 - Frob_w X)` at `w`. -/
def cmHarrisAdicFrobeniusEulerPolynomial : Rcoeff[X] :=
  FrobeniusPolynomial.frobeniusEulerPolynomial (K := F) w (adicCohomology degree)

/-- The Euler polynomial is the reversed characteristic polynomial of the geometric Frobenius
endomorphism along any closure embedding. -/
theorem cmHarrisAdicFrobeniusEulerPolynomial_eq_along
    (j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)) :
    cmHarrisAdicFrobeniusEulerPolynomial D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid w
        degree =
      (geometricFrobenius (ModuleCat.{0} Rcoeff) w (adicCohomology degree) j).hom.charpoly.reverse :=
  FrobeniusPolynomial.frobeniusEulerPolynomial_eq_along j

variable {w} in
/-- If every torsion stage is unramified at `w` along `j`, every geometric Frobenius lift acts on
the torsion limit with reversed characteristic polynomial the Frobenius Euler
polynomial. -/
theorem cmHarrisAdicFrobeniusEulerPolynomial_eq_of_lift
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : ∀ r, IsUnramifiedAlong (ModuleCat.{0} Rcoeff) w ((cohomologyAction degree).obj r) j)
    {g : LocalGroup w} (hg : IsGeometricFrobeniusLift w g) :
    ((adicCohomology degree).ρ (localRestriction w j g)).hom.charpoly.reverse =
      cmHarrisAdicFrobeniusEulerPolynomial D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid w
        degree :=
  FrobeniusPolynomial.eulerPolynomial_eq_frobeniusEulerPolynomial_of_lift
    (cmHarrisAdicCohomology_isUnramifiedAlong D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid degree hu)
    hg

end Frobenius

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
