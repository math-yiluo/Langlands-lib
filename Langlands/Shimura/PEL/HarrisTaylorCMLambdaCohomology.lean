import Langlands.Shimura.PEL.HarrisTaylorCMEllAdicGaloisCohomology
import Langlands.Shimura.ContinuousOrbitGaloisAction

/-! # The `λ`-adic cohomology of a geometric CM level with Harris's coefficient system

For a small CM level `U`, a degree `d` and a place `λ` of the coefficient field `K` above the
coefficient prime `ℓ`, the `K_λ`-vector space `H^d(S_U ×_F F̄, W)_λ` is the extension of scalars
of the published `ℓ`-power torsion limit `lim_r H^d(X̄_U, W_r)` along the `λ`-component
`∏_{λ' | ℓ} O_{K,λ'} → K_λ`, with the extended action of `Gal(F̄/F)`. No finiteness or freeness of
the torsion limit is assumed. The module also states, as propositions, finite dimensionality,
continuity for the `λ`-adic topology and unramifiedness of this action. See
`HarrisTaylorCMLambdaCohomology.md`.
-/

noncomputable section

universe wS wR uK uL uV

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

local notation "Klam" => FiniteCompletion K l.1

local notation "ellAdic" => cmHarrisEllAdicCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p existence geometry
  hRigid degree

/-! ## The `λ`-adic cohomology at a level -/

/-- The `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` of the geometric CM level `X̄_U` with Harris's
coefficient system `W`: the extension of scalars `K_λ ⊗ lim_r H^d(X̄_U, W_r)` of the `ℓ`-power
torsion limit along the `λ`-component `∏_{λ' | ℓ} O_{K,λ'} → K_λ`, with the extended action of
`Gal(F̄/F)`. -/
def cmHarrisLambdaCohomology :
    Action (ModuleCat.{0} (FiniteCompletion K l.1)) (Field.absoluteGaloisGroup F) :=
  letI := harrisCoefficientComponentAlgebra K p l
  LatticeGaloisRepresentation.baseChangeAction (L := FiniteCompletion K l.1) (ellAdic)

local notation "lambdaCoh" => cmHarrisLambdaCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p existence geometry
  hRigid l degree

/-- The space of the `λ`-adic cohomology is `K_λ ⊗ lim_r H^d(X̄_U, W_r)`, with `K_λ` an algebra
over the coefficient ring through the `λ`-component. -/
theorem cmHarrisLambdaCohomology_V :
    letI := harrisCoefficientComponentAlgebra K p l
    (lambdaCoh).V =
      ModuleCat.of (FiniteCompletion K l.1)
        (TensorProduct (HarrisCoefficientIntegers K p) (FiniteCompletion K l.1) (ellAdic).V) :=
  rfl

/-- A Galois element acts on `K_λ ⊗ lim_r H^d(X̄_U, W_r)` by the extension of scalars of its action
on the torsion limit. -/
theorem cmHarrisLambdaCohomology_ρ_hom (g : Field.absoluteGaloisGroup F) :
    letI := harrisCoefficientComponentAlgebra K p l
    ((lambdaCoh).ρ g).hom = ((ellAdic).ρ g).hom.baseChange (FiniteCompletion K l.1) :=
  rfl

/-- On pure tensors, a Galois element acts on the torsion-limit factor. -/
theorem cmHarrisLambdaCohomology_ρ_tmul (g : Field.absoluteGaloisGroup F)
    (a : FiniteCompletion K l.1) (x : (ellAdic).V) :
    letI := harrisCoefficientComponentAlgebra K p l
    ((lambdaCoh).ρ g).hom (a ⊗ₜ[HarrisCoefficientIntegers K p] x) =
      a ⊗ₜ[HarrisCoefficientIntegers K p] ((ellAdic).ρ g).hom x :=
  rfl

/-! ## Finiteness, continuity and unramifiedness as propositions -/

/-- `H^d(S_U ×_F F̄, W)_λ` is finite-dimensional over `K_λ`. -/
def CMHarrisLambdaCohomologyFiniteDimensional : Prop :=
  FiniteDimensional (FiniteCompletion K l.1) (lambdaCoh).V

/-- The action of `Gal(F̄/F)` on `H^d(S_U ×_F F̄, W)_λ` is continuous for the `λ`-adic topology:
each orbit map `g ↦ g · x` is continuous for the module topology over `K_λ`. -/
def CMHarrisLambdaCohomologyContinuous : Prop :=
  ContinuousGaloisAction.HasContinuousOrbits (lambdaCoh)

/-- The action of `Gal(F̄/F)` on `H^d(S_U ×_F F̄, W)_λ` is unramified at the finite place `w` of
`F`: the inertia group at `w` acts trivially. -/
def CMHarrisLambdaCohomologyUnramifiedAt (w : Global.FinitePlace F) : Prop :=
  IsUnramifiedAt (ModuleCat.{0} (FiniteCompletion K l.1)) w (lambdaCoh)

/-- The action of `Gal(F̄/F)` on `H^d(S_U ×_F F̄, W)_λ` is unramified at all but finitely many
finite places of `F`. -/
def CMHarrisLambdaCohomologyAlmostEverywhereUnramified : Prop :=
  ∃ S : Finset (Global.FinitePlace F), ∀ w ∉ S,
    CMHarrisLambdaCohomologyUnramifiedAt D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree w

/-- If every `ℓ`-power torsion stage is unramified at `w`, so is `H^d(S_U ×_F F̄, W)_λ`. -/
theorem cmHarrisLambdaCohomologyUnramifiedAt_of_stages (w : Global.FinitePlace F)
    (hu : ∀ r, IsUnramifiedAt (ModuleCat.{0} (HarrisCoefficientIntegers K p)) w
      ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p (harrisCoefficientPrime p)
        (harrisCoefficientPrime_ne_zero p) existence geometry hRigid degree).obj r)) :
    CMHarrisLambdaCohomologyUnramifiedAt D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p existence geometry hRigid l degree w :=
  letI := harrisCoefficientComponentAlgebra K p l
  LatticeGaloisRepresentation.isUnramifiedAlong_baseChange _
    (cmHarrisAdicCohomology_isUnramifiedAt D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p (harrisCoefficientPrime p)
      (harrisCoefficientPrime_ne_zero p) existence geometry hRigid degree hu)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
