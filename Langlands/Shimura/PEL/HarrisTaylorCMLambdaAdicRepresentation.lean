import Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology
import Langlands.Shimura.LatticeGaloisRepresentation

/-! # `l`-adic Galois representations from the torsion limit of Harris's CM coefficient system

The coefficient ring of Harris's torsion coefficient systems is the product of the valuation
rings at the places `l` of the coefficient field `K` above `p`. For each such place, extending
scalars of the `m`-power torsion limit `cmHarrisAdicCohomology` of the cohomology of a geometric
CM level along the `l`-component gives a Galois action on a finite-dimensional vector space over
the completion `K_l`. When the torsion limit is finite free and its matrix coefficients are
continuous, this is an `l`-adic Galois representation of `F` in the sense of
`Langlands.GaloisRepresentation.LambdaAdic`, and at a finite place where every torsion stage is
unramified its Euler polynomial is the image of the Frobenius Euler polynomial of the torsion
limit. No relation between the scalar `m` and `p` is assumed; when `m` is a unit at `l`, every
torsion stage has zero `l`-component. See `HarrisTaylorCMLambdaAdicRepresentation.md`.
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
open Langlands.Global AdelicFunctoriality
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt)

/-! ## The components of the coefficient ring -/

section Component

variable (K : Type) [Field K] [NumberField K] (p : Langlands.Global.FinitePlace ℚ)

/-- The ring map from the coefficient ring `∏_{l | p} O_{K,l}` to the completion `K_l` through
the `l`-component. -/
def harrisCoefficientComponentMap (l : FinitePlacesAbove K p) :
    HarrisCoefficientIntegers K p →+* FiniteCompletion K l.1 :=
  (algebraMap (CoefficientIntegers l.1) (FiniteCompletion K l.1)).comp
    (Pi.evalRingHom (fun l' : FinitePlacesAbove K p => CoefficientIntegers l'.1) l)

/-- The completion `K_l` as an algebra over the coefficient ring through the `l`-component. -/
abbrev harrisCoefficientComponentAlgebra (l : FinitePlacesAbove K p) :
    Algebra (HarrisCoefficientIntegers K p) (FiniteCompletion K l.1) :=
  (harrisCoefficientComponentMap K p l).toAlgebra

theorem harrisCoefficientComponentMap_apply (l : FinitePlacesAbove K p)
    (r : HarrisCoefficientIntegers K p) :
    harrisCoefficientComponentMap K p l r =
      algebraMap (CoefficientIntegers l.1) (FiniteCompletion K l.1) (r l) :=
  rfl

end Component

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



local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "adicCohomology" => cmHarrisAdicCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry
  hRigid

/-! ## The `l`-adic Galois representation -/

variable (l : FinitePlacesAbove K p) (degree : ℕ)

/-- The matrix coefficients of the `m`-power torsion limit, mapped to `K_l` through the
`l`-component, are continuous. -/
def CMHarrisAdicIsLatticeContinuous : Prop :=
  letI := harrisCoefficientComponentAlgebra K p l
  LatticeGaloisRepresentation.IsLatticeContinuous (L := FiniteCompletion K l.1)
    (cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability compatibility
      h htor q U ρ p m hm existence geometry hRigid degree)

variable [Module.Free (HarrisCoefficientIntegers K p)
    (cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U ρ p m hm existence geometry hRigid degree).V]
  [Module.Finite (HarrisCoefficientIntegers K p)
    (cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U ρ p m hm existence geometry hRigid degree).V]

/-- When the `m`-power torsion limit is finite free with continuous matrix coefficients, its
extension of scalars to `K_l` through the `l`-component, as an `l`-adic Galois representation of
`F`. -/
def cmHarrisLambdaAdicRepresentation
    (hcont : CMHarrisAdicIsLatticeContinuous D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid l
      degree) :
    GaloisRepresentation.LambdaAdic.{0, 0, 0} F K l.1 :=
  letI := harrisCoefficientComponentAlgebra K p l
  LatticeGaloisRepresentation.latticeObjects (adicCohomology degree) hcont

variable (hcont : CMHarrisAdicIsLatticeContinuous D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid l degree)

local notation "lambdaAdic" => cmHarrisLambdaAdicRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry
  hRigid l degree hcont

/-- A Galois element acts on `K_l ⊗ H` by the extension of scalars of its action on the torsion
limit `H`. -/
theorem cmHarrisLambdaAdicRepresentation_representation_apply (g : Field.absoluteGaloisGroup F) :
    letI := harrisCoefficientComponentAlgebra K p l
    (lambdaAdic).val.representation g = ((adicCohomology degree).ρ g).hom.baseChange _ :=
  rfl

/-- The dimension of the `l`-adic representation is the rank of the torsion limit. -/
theorem cmHarrisLambdaAdicRepresentation_rank [Nontrivial (HarrisCoefficientIntegers K p)] :
    (lambdaAdic).val.rank = Module.finrank Rcoeff (adicCohomology degree).V :=
  letI := harrisCoefficientComponentAlgebra K p l
  LatticeGaloisRepresentation.latticeObjects_rank _ hcont

/-- If every torsion stage is unramified at `w`, the `l`-adic representation has as Euler
polynomial at `w` the image in `K_l[X]` of the Frobenius Euler polynomial of the torsion
limit. -/
theorem cmHarrisLambdaAdicRepresentation_hasEulerPolynomialAt (w : Langlands.Global.FinitePlace F)
    (hu : ∀ r, IsUnramifiedAt (ModuleCat.{0} Rcoeff) w
      ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
        degree).obj r)) :
    GaloisRepresentation.HasEulerPolynomialAt (lambdaAdic) w
      ((cmHarrisAdicFrobeniusEulerPolynomial D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid w
        degree).map (harrisCoefficientComponentMap K p l)) :=
  letI := harrisCoefficientComponentAlgebra K p l
  LatticeGaloisRepresentation.hasEulerPolynomialAt_latticeObjects _ hcont w
    (cmHarrisAdicCohomology_isUnramifiedAt D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid degree hu)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
