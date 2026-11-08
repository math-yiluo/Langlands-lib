import Langlands.Shimura.PEL.HarrisTaylorCMLambdaAdicRepresentation

/-! # The coefficient-prime specialization of the torsion limit of Harris's CM coefficient system

Harris's torsion coefficients are reductions modulo the powers of the coefficient prime `ℓ`, the
residue characteristic of the rational place `p`. This module records that `ℓ` is a prime lying
in every place of the coefficient field above `p`, and specializes the `m`-power torsion limit of
the cohomology of a geometric CM level, its continuous Galois action and its `l`-adic Galois
representations to `m = ℓ`: the stages then have coefficients modulo `ℓ^r`, as in Harris. See
`HarrisTaylorCMEllAdicGaloisCohomology.md`.
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
open Langlands.Cohomology.HarrisCMCohomology (HarrisCMGaloisCohomologySmoothStatement)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt)

/-! ## The coefficient prime -/

section CoefficientPrime

variable (p : Langlands.Global.FinitePlace ℚ)

/-- The coefficient prime `ℓ` of a rational finite place `p`: its residue characteristic. -/
def harrisCoefficientPrime : ℕ :=
  GaloisRepresentation.residueCharacteristic p

/-- The coefficient prime lies in the place `p`. -/
theorem harrisCoefficientPrime_mem :
    ((harrisCoefficientPrime p : ℕ) : 𝓞 ℚ) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

/-- The coefficient prime is nonzero. -/
theorem harrisCoefficientPrime_ne_zero : harrisCoefficientPrime p ≠ 0 := by
  have : Finite (𝓞 ℚ ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot
  exact CharP.ringChar_ne_zero_of_finite _

/-- The coefficient prime is a prime number. -/
theorem harrisCoefficientPrime_prime : (harrisCoefficientPrime p).Prime :=
  (CharP.char_is_prime_or_zero (𝓞 ℚ ⧸ p.asIdeal) (ringChar (𝓞 ℚ ⧸ p.asIdeal))).resolve_right
    (harrisCoefficientPrime_ne_zero p)

variable {K : Type} [Field K] [NumberField K]

/-- The coefficient prime lies in every place of `K` above `p`. -/
theorem harrisCoefficientPrime_mem_above (l : FinitePlacesAbove K p) :
    ((harrisCoefficientPrime p : ℕ) : 𝓞 K) ∈ l.1.asIdeal := by
  have := l.2
  have h := (Ideal.mem_of_liesOver l.1.asIdeal p.asIdeal
    ((harrisCoefficientPrime p : ℕ) : 𝓞 ℚ)).1 (harrisCoefficientPrime_mem p)
  rwa [map_natCast] at h

end CoefficientPrime

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




local notation "Rcoeff" => HarrisCoefficientIntegers K p

/-! ## The `ℓ`-power torsion limit -/

/-- The `ℓ`-power torsion limit of the cohomology of degree `degree` of the geometric CM level
`X̄_U` with coefficients in the original stable-lattice coefficient system of `W`: the torsion
limit for the coefficient prime `ℓ` of `p`, whose stage `r` has coefficients modulo `ℓ^r`. -/
abbrev cmHarrisEllAdicCohomology (degree : ℕ) : Action (ModuleCat.{0} Rcoeff)
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
  cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility
    h htor q U ρ p (harrisCoefficientPrime p) (harrisCoefficientPrime_ne_zero p) existence
    geometry hRigid degree

/-- Under the Galois smoothness statement for the `ℓ`-power stages, the action of `Gal(F̄/F)` on
the `ℓ`-power torsion limit, with its inverse limit topology, is jointly continuous. -/
theorem continuous_cmHarrisEllAdicAction
    (hsmooth : HarrisCMGaloisCohomologySmoothStatement.{wS, wR} D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p
      (harrisCoefficientPrime p)
      (harrisCoefficientPrime_ne_zero p) existence geometry hRigid)
    (degree : ℕ) :
    Continuous fun x : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ×
        CMHarrisAdicSpace D C preservation composition unitCoherence associativity comparison
          symmetry stability square universality dualityNaturality polarizationStability
          compatibility h htor q U ρ p (harrisCoefficientPrime p)
          (harrisCoefficientPrime_ne_zero p) existence geometry
          hRigid degree =>
      ContinuousLimit.act (limit.cone (cmHarrisGeometricGaloisCohomologyAction D C preservation
        composition unitCoherence associativity comparison symmetry stability square
        universality dualityNaturality polarizationStability compatibility h htor q U ρ p
        (harrisCoefficientPrime p)
        (harrisCoefficientPrime_ne_zero p) existence geometry hRigid degree)) x.1 x.2 :=
  continuous_cmHarrisAdicAction D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q U ρ p (harrisCoefficientPrime p) (harrisCoefficientPrime_ne_zero p)
    existence geometry hRigid
    hsmooth degree

/-! ## The `l`-adic Galois representations -/

variable (l : FinitePlacesAbove K p) (degree : ℕ)
  [Module.Free (HarrisCoefficientIntegers K p)
    (cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U ρ p (harrisCoefficientPrime p) (harrisCoefficientPrime_ne_zero p)
      existence geometry hRigid degree).V]
  [Module.Finite (HarrisCoefficientIntegers K p)
    (cmHarrisAdicCohomology D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q U ρ p (harrisCoefficientPrime p) (harrisCoefficientPrime_ne_zero p)
      existence geometry hRigid degree).V]

/-- When the `ℓ`-power torsion limit is finite free with continuous matrix coefficients, its
extension of scalars to `K_l` through the `l`-component, an `l`-adic Galois representation of
`F` built from coefficients modulo the powers of the coefficient prime `ℓ` of `p`. -/
abbrev cmHarrisEllAdicRepresentation
    (hcont : CMHarrisAdicIsLatticeContinuous D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p (harrisCoefficientPrime p)
      (harrisCoefficientPrime_ne_zero p) existence geometry hRigid l degree) :
    GaloisRepresentation.LambdaAdic.{0, 0, 0} F K l.1 :=
  cmHarrisLambdaAdicRepresentation D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q U ρ p (harrisCoefficientPrime p) (harrisCoefficientPrime_ne_zero p)
    existence geometry hRigid l degree hcont

/-- If every `ℓ`-power torsion stage is unramified at `w`, the `l`-adic representation has as
Euler polynomial at `w` the image in `K_l[X]` of the Frobenius Euler polynomial of the `ℓ`-power
torsion limit. -/
theorem cmHarrisEllAdicRepresentation_hasEulerPolynomialAt
    (hcont : CMHarrisAdicIsLatticeContinuous D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p (harrisCoefficientPrime p)
      (harrisCoefficientPrime_ne_zero p) existence geometry hRigid l degree)
    (w : Langlands.Global.FinitePlace F)
    (hu : ∀ r, IsUnramifiedAt (ModuleCat.{0} Rcoeff) w
      ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p (harrisCoefficientPrime p)
        (harrisCoefficientPrime_ne_zero p)
        existence geometry hRigid degree).obj r)) :
    GaloisRepresentation.HasEulerPolynomialAt
      (cmHarrisEllAdicRepresentation D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q U ρ p existence geometry hRigid l degree hcont) w
      ((cmHarrisAdicFrobeniusEulerPolynomial D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U ρ p (harrisCoefficientPrime p)
        (harrisCoefficientPrime_ne_zero p)
        existence geometry hRigid w degree).map (harrisCoefficientComponentMap K p l)) :=
  cmHarrisLambdaAdicRepresentation_hasEulerPolynomialAt D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p (harrisCoefficientPrime p)
    (harrisCoefficientPrime_ne_zero p) existence geometry hRigid l degree hcont w hu

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
