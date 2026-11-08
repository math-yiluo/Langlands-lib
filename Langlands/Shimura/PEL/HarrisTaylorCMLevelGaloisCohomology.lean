import Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology
import Langlands.Shimura.LevelAutomorphismAction
import Langlands.Shimura.ContinuousGaloisAction

/-! # Galois actions on the cohomology of the actual CM tower at a fixed level

At a fixed sufficiently small CM level `U`, the Galois group of the CM field `F` acts on the
étale cohomology `H^d(X_U ×_F Spec F̄, p_U^* M)` of a sheaf `M` on `Spec F` pulled back to the
actual geometric CM scheme: an element acts by pullback along its automorphism of the
algebraic-closure factor. The action is natural in the sheaf, and the insertion of the level-`U`
cohomology into the published colimit over all small levels is Galois-equivariant. The same holds
at the levels of the prime-to-`m` tower. Over a topological field, a smooth finite-dimensional
fixed-level cohomology module is a continuous Galois representation of `F`, with its Euler
polynomials at unramified places. See `HarrisTaylorCMLevelGaloisCohomology.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
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
open Langlands.GaloisRepresentation (Objects ClosureEmbedding HasEulerPolynomialAt)
open Langlands.Shimura.DecompositionGroupAction (IsUnramifiedAt IsUnramifiedAlong
  geometricFrobenius)

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

local notation "base" => Spec (CommRingCat.of F)
local notation "Gamma" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
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

/-! ## The shrinking-level tower at a fixed level -/

section SmallLevel

variable (R : Type) [CommRing R] (U : SmallCMLevel D)

/-- The cohomology `H^d(X_U ×_F Spec F̄, p_U^* M)` of the actual geometric CM scheme at the fixed
level `U`, with sheaves pulled back from `Spec F`, with the action of `Gal(F̄/F)` by pullback
along its automorphisms of the algebraic-closure factor, natural in the sheaf. -/
def cmLevelGaloisCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤ Action (ModuleCat.{0} R) Gamma :=
  LevelAutomorphismAction.levelActionFunctor R arithmeticGeometricStructure galoisAction
    galoisOver U d

local notation "levelCohomology" => cmLevelGaloisCohomologyFunctor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q R U

@[simp] theorem cmLevelGaloisCohomologyFunctor_obj_V (d : ℕ) (M : ModuleSheaf base R) :
    ((levelCohomology d).obj M).V =
      (cohomology ((geometricSchemes).obj U) R d).obj
        ((EtaleInverseImage.inverseImage ((arithmeticGeometricStructure).app U) R).obj M) :=
  rfl

/-- A Galois element acts by the cohomological pullback along its automorphism of the CM
scheme at the level `U`, which is the automorphism of the algebraic-closure factor
(`cmSmallLevelGaloisAut_hom_app`). -/
theorem cmLevelGaloisCohomologyFunctor_ρ (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma) :
    ((levelCohomology d).obj M).ρ σ =
      LevelTowerCohomology.projectionCohomologyMap R ((arithmeticGeometricStructure).app U)
        ((arithmeticGeometricStructure).app U) ((galoisAction σ).unop.hom.app U)
        (NatTrans.congr_app (galoisOver σ) U) d M :=
  rfl

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

/-- The insertion of the level-`U` cohomology into the published colimit over all small levels
intertwines the Galois actions. -/
theorem cmLevelGaloisCohomology_ι_apply (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma)
    (x : ((levelCohomology d).obj M).V) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {U₁ V₁ : SmallCMLevel D} (k : U₁ ⟶ V₁), Etale ((geometricSchemes).map k) :=
      cmSmallLevelTowerEtale D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q existence geometry hRigid criterion
    SmoothRep.hom (((cmSmallLevelGaloisCohomologyFunctor D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid
        criterion R d).obj M).ρ σ)
        ((RestrictedLevelColimit.ι ((cmSmallLevelArithmeticCoefficients D C preservation
          composition unitCoherence associativity comparison symmetry stability square
          universality dualityNaturality polarizationStability compatibility h htor q existence
          geometry hRigid criterion R M).cohomology d) U).hom x) =
      (RestrictedLevelColimit.ι ((cmSmallLevelArithmeticCoefficients D C preservation
          composition unitCoherence associativity comparison symmetry stability square
          universality dualityNaturality polarizationStability compatibility h htor q existence
          geometry hRigid criterion R M).cohomology d) U).hom
        ((((levelCohomology d).obj M).ρ σ).hom x) :=
  cmSmallLevelGaloisCohomology_ρ_ι_apply D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q existence geometry hRigid criterion R d M σ U x

end SmallLevel

/-! ## The prime-to-`m` tower at a fixed level -/

section PrimeTo

variable (R : Type) [CommRing R] (m : ℕ) (hm : m ≠ 0)
  (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory)

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

/-- The cohomology of the actual geometric CM scheme at the prime-to-`m` level `K'`, that is at
the level `e⁻¹ (K₀ × K')`, with sheaves pulled back from `Spec F`, with the action of
`Gal(F̄/F)` by pullback along its automorphisms, natural in the sheaf. -/
def cmPrimeToLevelGaloisCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤ Action (ModuleCat.{0} R) Gamma :=
  LevelAutomorphismAction.levelActionFunctor R primeToStructure primeToGaloisAction
    primeToGaloisOver K' d

local notation "primeToLevelCohomology" => cmPrimeToLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q R m hm K₀ K'

@[simp] theorem cmPrimeToLevelGaloisCohomologyFunctor_obj_V (d : ℕ) (M : ModuleSheaf base R) :
    ((primeToLevelCohomology d).obj M).V =
      (cohomology ((primeToSchemes).obj K') R d).obj
        ((EtaleInverseImage.inverseImage ((primeToStructure).app K') R).obj M) :=
  rfl

/-- A Galois element acts by the cohomological pullback along its automorphism of the CM
scheme at the level `e⁻¹ (K₀ × K')` (`cmPrimeToGaloisAction_hom_app`). -/
theorem cmPrimeToLevelGaloisCohomologyFunctor_ρ (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma) :
    ((primeToLevelCohomology d).obj M).ρ σ =
      LevelTowerCohomology.projectionCohomologyMap R ((primeToStructure).app K')
        ((primeToStructure).app K') ((primeToGaloisAction σ).unop.hom.app K')
        (NatTrans.congr_app (primeToGaloisOver σ) K') d M :=
  rfl

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

/-- The insertion of the level-`K'` cohomology into the published prime-to-`m` colimit
intertwines the Galois actions. -/
theorem cmPrimeToLevelGaloisCohomology_ι_apply (d : ℕ) (M : ModuleSheaf base R) (σ : Gamma)
    (x : ((primeToLevelCohomology d).obj M).V) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {K₁ L₁ : (cmPrimeToProperty D m hm K₀).FullSubcategory} (a : K₁ ⟶ L₁),
        Etale ((primeToSchemes).map a) :=
      cmPrimeToTowerEtale D C preservation composition unitCoherence associativity comparison
        symmetry stability square universality dualityNaturality polarizationStability
        compatibility h htor q m hm K₀ existence geometry hRigid criterion
    SmoothRep.hom (((cmPrimeToGaloisCohomologyFunctor D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q m hm K₀ existence geometry
        hRigid criterion R d).obj M).ρ σ)
        ((RestrictedLevelColimit.ι ((cmPrimeToArithmeticCoefficients D C preservation
          composition unitCoherence associativity comparison symmetry stability square
          universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
          existence geometry hRigid criterion R M).cohomology d) K').hom x) =
      (RestrictedLevelColimit.ι ((cmPrimeToArithmeticCoefficients D C preservation
          composition unitCoherence associativity comparison symmetry stability square
          universality dualityNaturality polarizationStability compatibility h htor q m hm K₀
          existence geometry hRigid criterion R M).cohomology d) K').hom
        ((((primeToLevelCohomology d).obj M).ρ σ).hom x) :=
  cmPrimeToGaloisCohomology_ρ_ι_apply D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q m hm K₀ existence geometry hRigid criterion R d
    M σ K' x

end PrimeTo

/-! ## Continuous Galois representations at a fixed level -/

section SmallLevelGalois

variable (R : Type) [Field R] [TopologicalSpace R] (U : SmallCMLevel D) (d : ℕ)
  (M : ModuleSheaf (Spec (CommRingCat.of F)) R)

local notation "levelCohomology" => cmLevelGaloisCohomologyFunctor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q R U

/-- A smooth finite-dimensional fixed-level cohomology module over a topological field, as a
continuous Galois representation of `F`. -/
def cmLevelGaloisRepresentation
    (hsmooth : IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
      ((levelCohomology d).obj M)).ρ)
    [Module.Finite R ((levelCohomology d).obj M).V] :
    Objects.{0, 0, 0} F R :=
  ContinuousGaloisAction.toObjects (K := F) ((levelCohomology d).obj M) hsmooth

variable (hsmooth : IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
    ((cmLevelGaloisCohomologyFunctor D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q R U d).obj M)).ρ)
  [Module.Finite R ((cmLevelGaloisCohomologyFunctor D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q R U d).obj M).V]

local notation "levelGalois" => cmLevelGaloisRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q R U d M hsmooth

/-- The dimension of the Galois representation is that of the cohomology module. -/
theorem cmLevelGaloisRepresentation_rank :
    (levelGalois).val.rank = Module.finrank R ((levelCohomology d).obj M).V :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation has Euler polynomial `P` at `w` exactly when the fixed-level
cohomology is unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmLevelGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (levelGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{0} R) w ((levelCohomology d).obj M) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w ((levelCohomology d).obj M) = P :=
  ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff _ _ w

/-- If the fixed-level cohomology is unramified at `w` along `j`, the Euler polynomial at `w` is
the reversed characteristic polynomial of its geometric Frobenius endomorphism along `j`. -/
theorem cmLevelGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w ((levelCohomology d).obj M) j) :
    HasEulerPolynomialAt (levelGalois) w
      (geometricFrobenius (ModuleCat.{0} R) w ((levelCohomology d).obj M) j).hom.charpoly.reverse :=
  (ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff_along _ _ w j).2 ⟨hu, rfl⟩

end SmallLevelGalois

section PrimeToGalois

variable (R : Type) [Field R] [TopologicalSpace R] (m : ℕ) (hm : m ≠ 0)
  (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
  (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory) (d : ℕ)
  (M : ModuleSheaf (Spec (CommRingCat.of F)) R)

local notation "primeToLevelCohomology" => cmPrimeToLevelGaloisCohomologyFunctor D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q R m hm K₀ K'

/-- A smooth finite-dimensional cohomology module at the prime-to-`m` level `K'` over a
topological field, as a continuous Galois representation of `F`. -/
def cmPrimeToLevelGaloisRepresentation
    (hsmooth : IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
      ((primeToLevelCohomology d).obj M)).ρ)
    [Module.Finite R ((primeToLevelCohomology d).obj M).V] :
    Objects.{0, 0, 0} F R :=
  ContinuousGaloisAction.toObjects (K := F) ((primeToLevelCohomology d).obj M) hsmooth

variable (hsmooth : IsSmooth ((Rep.ActionToRep R (Field.absoluteGaloisGroup F)).obj
    ((cmPrimeToLevelGaloisCohomologyFunctor D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q R m hm K₀ K' d).obj M)).ρ)
  [Module.Finite R ((cmPrimeToLevelGaloisCohomologyFunctor D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q R m hm K₀ K' d).obj M).V]

local notation "primeToLevelGalois" => cmPrimeToLevelGaloisRepresentation D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q R m hm K₀ K' d M hsmooth

/-- The dimension of the Galois representation is that of the cohomology module. -/
theorem cmPrimeToLevelGaloisRepresentation_rank :
    (primeToLevelGalois).val.rank = Module.finrank R ((primeToLevelCohomology d).obj M).V :=
  rfl

variable (w : Global.FinitePlace F)

/-- The Galois representation has Euler polynomial `P` at `w` exactly when the cohomology at the
level `K'` is unramified at `w` with Frobenius Euler polynomial `P`. -/
theorem cmPrimeToLevelGaloisRepresentation_hasEulerPolynomialAt_iff {P : R[X]} :
    HasEulerPolynomialAt (primeToLevelGalois) w P ↔
      IsUnramifiedAt (ModuleCat.{0} R) w ((primeToLevelCohomology d).obj M) ∧
        FrobeniusPolynomial.frobeniusEulerPolynomial w ((primeToLevelCohomology d).obj M) = P :=
  ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff _ _ w

/-- If the cohomology at the level `K'` is unramified at `w` along `j`, the Euler polynomial at
`w` is the reversed characteristic polynomial of its geometric Frobenius endomorphism along
`j`. -/
theorem cmPrimeToLevelGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong
    {j : ClosureEmbedding (NumberField.FinitePlace.embedding (K := F) w)}
    (hu : IsUnramifiedAlong (ModuleCat.{0} R) w ((primeToLevelCohomology d).obj M) j) :
    HasEulerPolynomialAt (primeToLevelGalois) w
      (geometricFrobenius (ModuleCat.{0} R) w ((primeToLevelCohomology d).obj M)
        j).hom.charpoly.reverse :=
  (ContinuousGaloisAction.hasEulerPolynomialAt_toObjects_iff_along _ _ w j).2 ⟨hu, rfl⟩

end PrimeToGalois

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
