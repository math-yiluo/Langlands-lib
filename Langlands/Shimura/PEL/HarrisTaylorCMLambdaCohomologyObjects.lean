import Langlands.Shimura.PEL.HarrisTaylorCMLambdaCohomology
import Langlands.Shimura.ContinuousIsotypicGaloisRepresentation

/-! # The `λ`-adic cohomology of a geometric CM level as a `λ`-adic Galois representation

When the `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` of a small CM level `U` with Harris's
coefficient system `W` is finite-dimensional over `K_λ` and its Galois action has continuous
orbit maps for the `λ`-adic topology (the published propositions
`CMHarrisLambdaCohomologyFiniteDimensional` and `CMHarrisLambdaCohomologyContinuous`, taken here
as explicit hypotheses), it is a `λ`-adic Galois representation of `F`. At a finite place of `F`
where it is unramified, its Euler polynomial is the reversed characteristic polynomial of a
geometric Frobenius. See `HarrisTaylorCMLambdaCohomologyObjects.md`.
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
open Langlands.GaloisRepresentation (LambdaAdic ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt geometricFrobenius)
open Langlands.Shimura.ContinuousIsotypicGaloisRepresentation (continuousOrbitsObjects
  hasEulerPolynomialAt_continuousOrbitsObjects_iff
  hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong)

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
  (p : Global.FinitePlace ℚ)
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

variable (l : FinitePlacesAbove K p) (degree : ℕ)
  (hfin : CMHarrisLambdaCohomologyFiniteDimensional D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree)
  (hcont : CMHarrisLambdaCohomologyContinuous D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree)

set_option hygiene false in
local notation "lambdaCoh" => cmHarrisLambdaCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p existence geometry
  hRigid l degree

set_option hygiene false in
local notation "lambdaObj" => cmHarrisLambdaCohomologyObjects D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p existence geometry
  hRigid l degree hfin hcont

/-- The `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ`, when finite-dimensional over `K_λ` with
continuous Galois action, as a `λ`-adic Galois representation of `F`: the continuous
finite-dimensional representation of `Gal(F̄/F)` on its space. -/
def cmHarrisLambdaCohomologyObjects : LambdaAdic F K l.1 :=
  haveI : Module.Finite (FiniteCompletion K l.1) (lambdaCoh).V := hfin
  continuousOrbitsObjects (lambdaCoh) hcont

/-- A Galois element acts on the representation by its action on `H^d(S_U ×_F F̄, W)_λ`. -/
theorem cmHarrisLambdaCohomologyObjects_representation_apply
    (g : Field.absoluteGaloisGroup F) :
    (lambdaObj).val.representation g = ((lambdaCoh).ρ g).hom :=
  rfl

/-- The dimension of the representation is the dimension of `H^d(S_U ×_F F̄, W)_λ` over `K_λ`. -/
theorem cmHarrisLambdaCohomologyObjects_rank :
    (lambdaObj).val.rank = Module.finrank (FiniteCompletion K l.1) (lambdaCoh).V :=
  rfl

/-- The representation has Euler polynomial `P` at a finite place `v` of `F` exactly when
`H^d(S_U ×_F F̄, W)_λ` is unramified at `v` and `P` is its Frobenius Euler polynomial. -/
theorem hasEulerPolynomialAt_cmHarrisLambdaCohomologyObjects_iff (v : Global.FinitePlace F)
    {P : (FiniteCompletion K l.1)[X]} :
    haveI : Module.Finite (FiniteCompletion K l.1) (lambdaCoh).V := hfin
    HasEulerPolynomialAt (lambdaObj) v P ↔
      CMHarrisLambdaCohomologyUnramifiedAt D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree v ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial v (lambdaCoh) = P :=
  haveI : Module.Finite (FiniteCompletion K l.1) (lambdaCoh).V := hfin
  hasEulerPolynomialAt_continuousOrbitsObjects_iff (lambdaCoh) hcont v

/-- At a finite place `v` of `F` where `H^d(S_U ×_F F̄, W)_λ` is unramified, the Euler polynomial
of the representation is the reversed characteristic polynomial of a geometric Frobenius at `v`,
along any closure embedding at `v` (Harris 1999, formula (5.6)). -/
theorem hasEulerPolynomialAt_cmHarrisLambdaCohomologyObjects {v : Global.FinitePlace F}
    (ι : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) v))
    (hu : CMHarrisLambdaCohomologyUnramifiedAt D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree v) :
    haveI : Module.Finite (FiniteCompletion K l.1) (lambdaCoh).V := hfin
    HasEulerPolynomialAt (lambdaObj) v
      (geometricFrobenius (ModuleCat.{0} (FiniteCompletion K l.1)) v (lambdaCoh)
        ι).hom.charpoly.reverse :=
  haveI : Module.Finite (FiniteCompletion K l.1) (lambdaCoh).V := hfin
  hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong (lambdaCoh) hcont v
    ((DecompositionGroupAction.isUnramifiedAt_iff_along (lambdaCoh) ι).1 hu)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
