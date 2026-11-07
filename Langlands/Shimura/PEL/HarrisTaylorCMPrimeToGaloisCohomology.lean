import Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology
import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients
import Langlands.Shimura.RestrictedReindexTowerAutomorphisms
import Langlands.Shimura.LevelHeckeModule

/-! # Galois action and Hecke modules on the prime-to-`m` cohomology of the actual CM tower

The Galois automorphisms of the actual geometric CM tower over `Spec F` restrict to the
prime-to-`m` tower `K' ↦ Sh(e⁻¹ (K₀ × K'))`. On its colimit cohomology with coefficients pulled
back from `Spec F` they act by pullback, commuting with `GG(A_f^{(m)})ᵐᵒᵖ` and with the comparison
to the shrinking-level cohomology of the CM tower. The fixed vectors under a prime-to-`m` level
`K'` are modules over the Hecke algebra of `K'` with the commuting Galois action. See
`HarrisTaylorCMPrimeToGaloisCohomology.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel RestrictedSplitLevelTowerCohomology
open Langlands.Geometry.EtaleDerivedSections

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

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "arithmeticStructure" => cmSmallLevelArithmeticStructure D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "arithmeticGeometricStructure" => cmSmallLevelArithmeticGeometricStructure D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
local notation "galoisAction" => cmSmallLevelGaloisAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "galoisOver" => cmSmallLevelGaloisAction_over D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "selfTrivial" => cmGeometricSchemeTower_restrictedSelfArrow D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "small" => D.rationalInvolution.LevelSufficientlySmall
local notation "Fbar" => AlgebraicClosure F
local notation "base" => Spec (CommRingCat.of F)
local notation "Gamma" => (Fbar ≃ₐ[F] Fbar)

variable (m : ℕ) (hm : m ≠ 0)

/-! ## The Galois action on the prime-to-`m` tower -/

section Tower

variable (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)

local notation "primeToSchemes" => cmPrimeToSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀

/-- The projections of the prime-to-`m` tower to `Spec F`: at level `K'`, the projection of the
actual geometric CM scheme at level `e⁻¹ (K₀ × K')`. -/
def cmPrimeToArithmeticStructure :
    primeToSchemes ⟶ (Functor.const (cmPrimeToProperty D m hm K₀).FullSubcategory).obj base :=
  RestrictedReindexLevelTowerCohomology.reindexProjection (awayOver (cmPrimeToSplit D m hm) K₀)
    ((awayOver (cmPrimeToSplit D m hm) K₀).mapsTo_inverseImage (P := small))
    arithmeticGeometricStructure

@[simp] theorem cmPrimeToArithmeticStructure_app
    (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory) :
    (cmPrimeToArithmeticStructure D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀).app K' =
      (arithmeticGeometricStructure).app ((awayFunctor (cmPrimeToSplit D m hm) small K₀).obj K') :=
  rfl

/-- The Galois group of `F` acts on the prime-to-`m` tower by the restrictions of its action on
the actual geometric CM tower. -/
def cmPrimeToGaloisAction : Gamma →* (Aut primeToSchemes)ᵐᵒᵖ :=
  awayAutomorphisms (cmPrimeToSplit D m hm) K₀ galoisAction

/-- At level `K'`, a Galois element acts on the algebraic-closure factor of the actual CM scheme
at level `e⁻¹ (K₀ × K')`. -/
@[simp] theorem cmPrimeToGaloisAction_hom_app (σ : Gamma)
    (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory) :
    (cmPrimeToGaloisAction D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q m hm K₀ σ).unop.hom.app K' =
      EtaleGaloisAction.baseChangeMap
        ((arithmeticStructure).app ((awayFunctor (cmPrimeToSplit D m hm) small K₀).obj K')) σ :=
  cmSmallLevelGaloisAut_hom_app D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q σ _

/-- Every Galois automorphism of the prime-to-`m` tower is over `Spec F`. -/
theorem cmPrimeToGaloisAction_over (σ : Gamma) :
    (cmPrimeToGaloisAction D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q m hm K₀ σ).unop.hom ≫
        cmPrimeToArithmeticStructure D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ =
      cmPrimeToArithmeticStructure D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ :=
  awayAutomorphisms_over (cmPrimeToSplit D m hm) K₀ galoisAction galoisOver σ

end Tower

/-! ## Arithmetic coefficients and the Galois action on cohomology -/

section Cohomology

variable (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)

local notation "primeToSchemes" => cmPrimeToSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
local notation "primeToStructure" => cmPrimeToArithmeticStructure D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
local notation "primeToGaloisAction" => cmPrimeToGaloisAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
local notation "primeToGaloisOver" => cmPrimeToGaloisAction_over D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
local notation "primeToSelfTrivial" => cmPrimeToSchemeTower_restrictedSelfArrow D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q m hm K₀

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

include existence geometry hRigid criterion

local notation "towerEtale" => cmSmallLevelTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion
local notation "primeToEtale" => cmPrimeToTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion

variable (R : Type) [CommRing R]

local notation "arithmeticCoefficients" => cmSmallLevelArithmeticCoefficients D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R
local notation "primeToCoefficients" => cmPrimeToCoefficientDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R
local notation "primeToTrivialCoefficients" => cmPrimeToTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- Sheaves on `Spec F` pulled back to every level of the prime-to-`m` tower, with the
restriction/projection comparisons along its transition maps. -/
def cmPrimeToArithmeticCoefficients (M : ModuleSheaf base R) : primeToCoefficients :=
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  RestrictedLevelTowerCohomology.canonicalCoefficients R primeToStructure M

local notation "primeToArithmeticCoefficients" => cmPrimeToArithmeticCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- These are the arithmetic coefficients of the actual CM tower, restricted to the levels
`e⁻¹ (K₀ × K')`. -/
theorem cmPrimeToArithmeticCoefficients_eq (M : ModuleSheaf base R) :
    primeToArithmeticCoefficients M =
      cmPrimeToCoefficients D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R (arithmeticCoefficients M) := by
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact (awayCoefficients_canonical (cmPrimeToSplit D m hm) K₀ arithmeticGeometricStructure M).symm

/-- The arithmetic coefficients on the prime-to-`m` tower are level-trivial. -/
theorem cmPrimeToArithmeticCoefficients_trivial (M : ModuleSheaf base R) :
    primeToTrivialCoefficients (primeToArithmeticCoefficients M) := by
  let : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact RestrictedLevelTowerCohomology.isLevelTrivialCoefficients_canonical R primeToSelfTrivial M

/-- The prime-to-`m` colimit cohomology of sheaves pulled back from `Spec F`, as smooth
representations of `GG(A_f^{(m)})ᵐᵒᵖ`, natural in the sheaf. -/
def cmPrimeToArithmeticCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤ SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact RestrictedLevelTowerCohomology.smoothCanonicalCohomologyFunctor
    R primeToStructure primeToSelfTrivial d

local notation "primeToArithmeticCohomologyFunctor" => cmPrimeToArithmeticCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

/-- This is the prime-to-`m` smooth cohomology of the arithmetic coefficients. -/
@[simp] theorem cmPrimeToArithmeticCohomologyFunctor_obj (d : ℕ) (M : ModuleSheaf base R) :
    (primeToArithmeticCohomologyFunctor d).obj M =
      cmPrimeToSmoothCohomology D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R (primeToArithmeticCoefficients M)
        (cmPrimeToArithmeticCoefficients_trivial D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
          criterion R M) d :=
  rfl

/-- The prime-to-`m` colimit cohomology of sheaves pulled back from `Spec F`, with the commuting
action of the Galois group of `F` by pullback along the Galois automorphisms of the prime-to-`m`
tower, natural in the sheaf. -/
def cmPrimeToGaloisCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤
      Action (SmoothRep.{0, 0, 0} R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) Gamma := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact RestrictedLevelTowerCohomology.automorphismActionFunctor
    R primeToStructure primeToSelfTrivial primeToGaloisAction primeToGaloisOver d

local notation "primeToGaloisCohomologyFunctor" => cmPrimeToGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R

@[simp] theorem cmPrimeToGaloisCohomologyFunctor_obj_V (d : ℕ) (M : ModuleSheaf base R) :
    ((primeToGaloisCohomologyFunctor d).obj M).V = (primeToArithmeticCohomologyFunctor d).obj M :=
  rfl

/-- Forgetting the Galois action gives the prime-to-`m` smooth cohomology functor. -/
def cmPrimeToGaloisCohomologyForgetIso (d : ℕ) :
    primeToGaloisCohomologyFunctor d ⋙ Action.forget _ Gamma ≅
      primeToArithmeticCohomologyFunctor d :=
  Iso.refl _

/-- A Galois element acts by smooth pullback along its automorphism of the prime-to-`m`
tower. -/
theorem cmPrimeToGaloisCohomologyFunctor_ρ (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
        Etale ((primeToSchemes).map a) :=
      primeToEtale
    ((primeToGaloisCohomologyFunctor d).obj M).ρ σ =
      (RestrictedLevelTowerCohomology.smoothCanonicalPullback R primeToStructure
        (primeToGaloisAction σ).unop.hom (primeToGaloisOver σ)
        primeToSelfTrivial primeToSelfTrivial d).app M := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  rfl

/-- At a prime-to-`m` level `K'`, a Galois element acts by the cohomological pullback along its
automorphism of the actual CM scheme at level `e⁻¹ (K₀ × K')`. -/
theorem cmPrimeToGaloisCohomology_ρ_ι_apply (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma)
    (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory)
    (x : (EtaleDerivedSections.cohomology ((primeToSchemes).obj K') R d).obj
      ((EtaleInverseImage.inverseImage ((primeToStructure).app K') R).obj M)) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
        Etale ((primeToSchemes).map a) :=
      primeToEtale
    SmoothRep.hom (((primeToGaloisCohomologyFunctor d).obj M).ρ σ)
        ((RestrictedLevelColimit.ι ((primeToArithmeticCoefficients M).cohomology d) K').hom x) =
      (RestrictedLevelColimit.ι ((primeToArithmeticCoefficients M).cohomology d) K').hom
        ((LevelTowerCohomology.projectionCohomologyMap R
          ((primeToStructure).app K') ((primeToStructure).app K')
          ((primeToGaloisAction σ).unop.hom.app K') (NatTrans.congr_app (primeToGaloisOver σ) K')
          d M).hom x) := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact congrArg (fun f => f.hom x)
    (RestrictedLevelTowerCohomology.canonicalPullback_ι R primeToStructure
      (primeToGaloisAction σ).unop.hom (primeToGaloisOver σ) M d K')

/-- The Galois action commutes with the action of `GG(A_f^{(m)})ᵐᵒᵖ`. -/
theorem cmPrimeToGaloisCohomology_commutes (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma)
    (g : (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)
    (x : ((primeToGaloisCohomologyFunctor d).obj M).V) :
    SmoothRep.hom (((primeToGaloisCohomologyFunctor d).obj M).ρ σ)
        (((primeToGaloisCohomologyFunctor d).obj M).V.obj.ρ g x) =
      ((primeToGaloisCohomologyFunctor d).obj M).V.obj.ρ g
        (SmoothRep.hom (((primeToGaloisCohomologyFunctor d).obj M).ρ σ) x) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom (((primeToGaloisCohomologyFunctor d).obj M).ρ σ)) g x

/-- The comparison from the prime-to-`m` cohomology to the shrinking-level cohomology of the
actual CM tower commutes with the Galois action. -/
theorem cmPrimeToGaloisCohomologyComparison_apply (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma)
    (x : ((primeToGaloisCohomologyFunctor d).obj M).V.obj) :
    (cmPrimeToCohomologyComparison D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
        criterion R (arithmeticCoefficients M) d).hom.hom
        ((((primeToGaloisCohomologyFunctor d).obj M).ρ σ).hom.hom x) =
      (((galoisCohomologyFunctor d).obj M).ρ σ).hom.hom
        ((cmPrimeToCohomologyComparison D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid
          criterion R (arithmeticCoefficients M) d).hom.hom x) := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact automorphism_awayComparison_apply (cmPrimeToSplit D m hm) K₀ galoisAction galoisOver R
    selfTrivial d M σ x

/-! ## Hecke modules -/

variable (K' : CompactOpenLevel (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)

/-- The `K'`-fixed vectors of the prime-to-`m` cohomology of sheaves pulled back from `Spec F`,
as modules over the Hecke algebra of `K'` with the commuting Galois action, natural in the
sheaf. -/
def cmPrimeToGaloisHeckeModuleFunctor (d : ℕ) :
    ModuleSheaf base R ⥤
      Action (ModuleCat.{0} (LevelHecke.LevelHeckeAlgebra R K'.subgroup)) Gamma := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {K L : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K ⟶ L),
      Etale ((primeToSchemes).map a) :=
    primeToEtale
  exact LevelHecke.restrictedAutomorphismHeckeModuleFunctor R primeToStructure
    primeToSelfTrivial K' primeToGaloisAction primeToGaloisOver d

local notation "primeToGaloisHeckeModuleFunctor" => cmPrimeToGaloisHeckeModuleFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
  existence geometry hRigid criterion R K'

/-- The Hecke module functor is the Galois cohomology functor followed by taking `K'`-fixed
vectors as Hecke modules. -/
theorem cmPrimeToGaloisHeckeModuleFunctor_eq (d : ℕ) :
    primeToGaloisHeckeModuleFunctor d =
      primeToGaloisCohomologyFunctor d ⋙
        LevelHecke.heckeModuleActionFunctor R Gamma K'.subgroup :=
  rfl

/-- Restricting the scalars from the Hecke algebra to `R` gives the `K'`-fixed vectors with the
Galois action. -/
def cmPrimeToGaloisHeckeModuleForgetIso (d : ℕ) :
    primeToGaloisHeckeModuleFunctor d ⋙
        (ModuleCat.restrictScalars
          (algebraMap R (LevelHecke.LevelHeckeAlgebra R K'.subgroup))).mapAction Gamma ≅
      primeToGaloisCohomologyFunctor d ⋙ LevelHecke.fixedVectorsActionFunctor R Gamma K'.subgroup :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (LevelHecke.heckeModuleActionForgetIso R Gamma K'.subgroup)

/-- Each Galois element commutes with every element of the Hecke algebra of `K'`. -/
theorem cmPrimeToGaloisHeckeModule_ρ_smul (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma)
    (a : LevelHecke.LevelHeckeAlgebra R K'.subgroup)
    (x : ((primeToGaloisHeckeModuleFunctor d).obj M).V) :
    (((primeToGaloisHeckeModuleFunctor d).obj M).ρ σ).hom (a • x) =
      a • (((primeToGaloisHeckeModuleFunctor d).obj M).ρ σ).hom x :=
  map_smul _ a x

/-- The double-coset element `[K' g K']` acts as the double-coset operator on the
`K'`-fixed vectors. -/
theorem cmPrimeToGaloisHeckeModule_doubleCoset_smul (d : ℕ) (M : ModuleSheaf base R)
    (g : (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ)
    (x : fixedVectors ((primeToGaloisCohomologyFunctor d).obj M).V.obj.ρ
      K'.subgroup) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    (LevelHecke.doubleCoset K' g : LevelHecke.LevelHeckeAlgebra R K'.subgroup) •
        (show ((primeToGaloisHeckeModuleFunctor d).obj M).V from x) =
      ((LevelHecke.heckeActionNatTrans R Gamma K' K' g).app
        ((primeToGaloisCohomologyFunctor d).obj M)).hom x := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  exact LevelHecke.doubleCoset_smul_heckeActionNatTrans Gamma K' g _ x

end Cohomology

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
