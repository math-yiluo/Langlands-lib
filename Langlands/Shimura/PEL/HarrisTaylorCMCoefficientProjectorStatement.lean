import Langlands.Shimura.PEL.AbelianPowerGaloisOperators
import Langlands.Shimura.PEL.HarrisTaylorCMUniversalClass
import Langlands.Shimura.PEL.HarrisTaylorCMLambdaCohomology
import Langlands.Galois.CyclotomicTwist

/-!
# Realization of algebraic coefficients by projectors on the actual CM levels

Harris–Taylor III.2, p. 98, on the represented componentwise abelian powers.
The coefficient comparison is stated after extending the finite completion
to its algebraic closure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe wS wR wGeo wPadic

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
open Langlands.Global AdelicFunctoriality
open Langlands.Global.CompletionPadic (residuePrime)
open Langlands.GaloisRepresentation (absoluteCyclotomicCharacter)
open Langlands.Cohomology.AbelianPower

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


variable (lam : FinitePlacesAbove K p)

local notation "Klam" => FiniteCompletion K lam.1
local notation "Λ" => AlgebraicClosure Klam
local notation "ell" => residuePrime lam.1

local notation "rep" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U

private abbrev projectorComponents := _root_.ConnectedComponents (rep).base.obj.left

local notation "Component" => projectorComponents D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U

local notation "component" => componentCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (rep).base

local notation "family" => cmUniversalAbelianFamily D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor (rep)

local notation "representative" => cmUniversalRepresentative D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor (rep)

/-- The PEL action on the chosen abelian representative over a component. -/
abbrev cmProjectorPEL (c : Component) : A →+* End0 (family c) :=
  letI := auxiliaryStarRing D C
  (representative c).1.actionObj.action.toRingHom

private abbrev geometricCoefficientMap : ℚ_[ell] →+* Λ :=
  (algebraMap Klam Λ).comp (Langlands.Global.CompletionPadic.padicMap lam.1)

/-- The residue prime used for the geometric coefficient map is the prime
used in the Harris coefficient system. -/
theorem cmProjectorCoefficientPrime : ell = harrisCoefficientPrime p :=
  let : Fact (harrisCoefficientPrime p).Prime := ⟨harrisCoefficientPrime_prime p⟩
  Langlands.Global.residuePrime_eq_of_natCast_mem lam.1
    (harrisCoefficientPrime_mem_above p lam)

variable [geomDerived : ∀ X : Scheme.{0}, HasDerivedCategory.{wGeo}
  (EtaleDerivedSections.ModuleSheaf X ℤ_[residuePrime lam.1])]
variable [padicDerived : HasDerivedCategory.{wPadic} (ModuleCat ℤ_[residuePrime lam.1])]

private abbrev powerCohomology (c : Component) (m i : ℕ) :=
  cohomologyAction.{wGeo, wPadic} (family c) (component c).obj.hom m ell
    (geometricCoefficientMap p lam) i

private abbrev projector (c : Component) {m : ℕ}
    (e : FreeAlgebra Λ (GeometricOperator A m)) (i : ℕ) :=
  projectedPELAction.{wGeo, wPadic} (family c) (component c).obj.hom m ell
    (geometricCoefficientMap p lam) (cmProjectorPEL D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U c) (2 * Module.finrank ℚ E * n^2) i e

private abbrev tateScalar (t : ℕ) (σ : Field.absoluteGaloisGroup F) : Λ :=
  ((geometricCoefficientMap p lam).comp (PadicInt.Coe.ringHom (p := ell)))
    ((absoluteCyclotomicCharacter ell F σ).val ^ t)

variable [HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
variable [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

private abbrev coefficientCohomology (i : ℕ) : Action (ModuleCat Λ) (Field.absoluteGaloisGroup F) :=
  ((ModuleCat.extendScalars (algebraMap Klam Λ)).mapAction _).obj
    (cmHarrisLambdaCohomology.{wS, wR} D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U ρ p existence geometry hRigid lam i)

/-- Geometric coefficient realization at a represented CM level. The same
projector expression is used on every component in all degrees. The
Galois comparison uses the positive cyclotomic twist. Scalars of weight
`-w` in `ρ` have weight `w` after transport to the right frame group. -/
def HarrisCMGeometricCoefficientProjectorStatement (w : ℤ) : Prop :=
  (∀ a : A, a ≠ 0 → IsUnit a) →
  Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (ρ.act (AlgebraicClosure K))) →
  (∀ (g : (D.rationalInvolution.baseChange K).similitudes) (t : Kˣ),
    ((g.1.1 : K ⊗[ℚ] A) = algebraMap K (K ⊗[ℚ] A) t) →
      ∀ x : W, ρ.rationalAction g x = ((t : K) ^ (-w)) • x) →
  ∃ (m t : ℕ) (e : FreeAlgebra Λ (GeometricOperator A m)),
    (2 * (t : ℤ) - (m : ℤ) = w) ∧
    (∀ (c : Component) (j : ℕ), IsIdempotentElem
      (projector.{wGeo, wPadic} D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q U p lam c e j)) ∧
    ∀ i : ℕ,
      let V := coefficientCohomology.{wS, wR} D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p existence geometry hRigid lam i
      let P c := projector.{wGeo, wPadic} D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q U p lam c e (i + m)
      ∃ Φ : V.V ≃ₗ[Λ] (∀ c : Component, (P c).range),
        ∀ (σ : Field.absoluteGaloisGroup F) (x : V.V) (c : Component),
          (Φ ((V.ρ σ).asHom.hom x) c).val = tateScalar (F := F) p lam t σ •
            ((powerCohomology.{wGeo, wPadic} D C preservation composition unitCoherence
              associativity comparison symmetry stability square universality dualityNaturality
              polarizationStability compatibility h htor q U p lam c m (i + m)).ρ σ).asHom.hom
                (Φ x c).val

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
