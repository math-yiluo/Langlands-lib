import Langlands.Shimura.PEL.HarrisTaylorCMKottwitzStatement
import Langlands.Galois.Local.LabelledHodgeTate

/-! # Labelled Hodge–Tate decomposition of the Harris middle-degree multiplicity

At every coefficient place `λ` and every embedding `j` of the CM field into
the coefficient field, the actual degree-`n - 1` Hecke multiplicity
representation of `πf` is labelled Hodge–Tate at `λ ∘ j`, with `n` distinct
exponents of a common multiplicity `m` and `n m` equal to its dimension. See
the paired Markdown.
-/

noncomputable section

universe wS wR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Global AdelicFunctoriality
open Langlands.Shimura.CompactOpenLevel Langlands.Shimura.RestrictedLevelColimit
open Langlands.Shimura.SmallLevelGaloisTower
open Langlands.Shimura.IsotypicGaloisAction
open Langlands.Shimura.ContinuousIsotypicGaloisRepresentation
open Langlands.GaloisRepresentation (Objects HasEulerPolynomialAt HasLabelledHodgeTateAt)
open Langlands.Shimura.KottwitzUnramified (UnramifiedChart LocalPoints SqrtPrime)
open Langlands.Shimura.KottwitzDual (IsKottwitzPolynomial)
open Langlands.Cohomology.Weights (IsWeilNumber IsPurePolynomial)

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

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)
  (U : SmallCMLevel D)

set_option hygiene false in
/-- Harris's CM-type section `Φ`. -/
local notation "Φ" => harrisCMSection E (algebraMap L F) τ₀

set_option hygiene false in
local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

set_option hygiene false in
/-- The derived-category instances of the Library's `λ`-adic cohomology for the coefficient
prime `ℓ`. -/
local notation "derivedInstances" ℓ =>
  ∀ U' : SmallCMLevel D, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U')
        (HarrisCoefficientIntegers K ℓ))

set_option hygiene false in
/-- `π_f ⊗_K K_λ`. -/
local notation "τλ" =>
  (Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp πf

set_option hygiene false in
local notation "towerλ" => cmHarrisLambdaTowerExtendScalars D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry hRigid
  lam i (FiniteCompletion K lam.1)

set_option hygiene false in
/-- The place `v` of `F` determined by `θ`, via `Φ τ₁ : F → ℂ`. -/
local notation "vθ" => (harrisPlace p₀ θ (Φ C.distinguished)).1


/-- Coefficient-equivariant labelled Hodge–Tate decomposition of the actual
middle-degree Hecke multiplicity representation, at every coefficient place
and every label. -/
def HarrisCMLabelledMultiplicityStatement : Prop :=
  ∀ (_hdiv : ∀ a : A, a ≠ 0 → IsUnit a)
    (_hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished)
    (_hρ : Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ρ.act (AlgebraicClosure K))))
    (w : ℤ)
    (_hw : ∀ (g : (D.rationalInvolution.baseChange K).similitudes) (t : Kˣ),
      ((g.1.1 : K ⊗[ℚ] A) = algebraMap K (K ⊗[ℚ] A) t) →
        ∀ x : W, ρ.rationalAction g x = ((t : K) ^ (-w)) • x)
    {V : Type} [AddCommGroup V] [Module K V]
    (πf : Representation K D.rationalInvolution.FiniteAdelicPoints V)
    (_hadm : Langlands.IsAdmissible πf)
    (_hirr : Representation.IsIrreducible
      ((Module.End.baseChangeHom K (AlgebraicClosure K) V).toMonoidHom.comp πf)),
    (∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances ℓ]
      [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
      (lam : FinitePlacesAbove K ℓ),
      (∀ i : ℕ, CMHarrisLambdaTowerFixedVectorComparison D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence geometry
        hRigid lam i) →
      ∀ i : ℕ, i ≠ n - 1 →
        Subsingleton (cmHarrisLambdaTowerHeckeMultiplicity D C preservation
          composition unitCoherence associativity comparison symmetry stability square
          universality dualityNaturality polarizationStability compatibility h htor q ℓ ρ
          existence geometry hRigid lam i (FiniteCompletion K lam.1) (τλ) U).V) →
    ∀ (ℓ : Global.FinitePlace ℚ) [derivedInstances ℓ]
      [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K ℓ))]
      (lam : FinitePlacesAbove K ℓ)
      (hfix : ∀ i : ℕ, CMHarrisLambdaTowerFixedVectorComparison D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor q ℓ ρ
        existence geometry hRigid lam i)
      (hcont : ∀ i : ℕ, CMHarrisLambdaCohomologyContinuous D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ ℓ existence
        geometry (hRigid U) lam i)
      [Module.Finite (FiniteCompletion K lam.1)
        (fixedVectors ((Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp
            πf) (inverseOpposite U.obj).subgroup →ₗ[
          Langlands.Shimura.LevelHecke.LevelHeckeAlgebra (FiniteCompletion K lam.1)
            (inverseOpposite U.obj).subgroup]
          fixedVectors (cmHarrisLambdaTowerExtendScalars D C preservation composition
            unitCoherence associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence
            geometry hRigid lam (n - 1) (FiniteCompletion K lam.1)).V.representation
            (inverseOpposite U.obj).subgroup)]
      (j : F →+* K),
      ∃ (m : ℕ) (k : Fin n → ℤ), Function.Injective k ∧
        n * m = Module.finrank (FiniteCompletion K lam.1)
          (fixedVectors ((Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp
              πf) (inverseOpposite U.obj).subgroup →ₗ[
            Langlands.Shimura.LevelHecke.LevelHeckeAlgebra (FiniteCompletion K lam.1)
              (inverseOpposite U.obj).subgroup]
            fixedVectors (cmHarrisLambdaTowerExtendScalars D C preservation composition
              unitCoherence associativity comparison symmetry stability square universality
              dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence
              geometry hRigid lam (n - 1) (FiniteCompletion K lam.1)).V.representation
              (inverseOpposite U.obj).subgroup) ∧
        HasLabelledHodgeTateAt lam.1
          (cmHarrisLambdaHeckeMultiplicityObjects D C preservation composition
            unitCoherence associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor q ℓ ρ existence
            geometry hRigid lam (n - 1) (FiniteCompletion K lam.1) continuous_id
            (hfix (n - 1)) U (hcont (n - 1))
            ((Module.End.baseChangeHom K (FiniteCompletion K lam.1) V).toMonoidHom.comp πf))
          ((NumberField.FinitePlace.embedding lam.1).comp j) n m k

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
