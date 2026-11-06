import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelBaseCoefficients
import Langlands.Shimura.RestrictedLevelTowerGalois

/-! # Galois actions on base-field coefficients of actual small CM levels -/

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
open CompactOpenLevel
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

local notation "schemes" => cmSchemeTower D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q
local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q
local notation "chosen" => chosenCMLevelRepresentation D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q
local notation "overTower" => representedCMOverTower D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor chosen
local notation "projection" => cmGeometricProjection D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q
local notation "geometricStructure" => cmSmallLevelGeometricStructure D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q
local notation "small" => D.rationalInvolution.LevelSufficientlySmall
local notation "G" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "Fbar" => AlgebraicClosure F
local notation "base" => Spec (CommRingCat.of F)
local notation "Gamma" => (Fbar ≃ₐ[F] Fbar)

/-- The structure maps of the original represented CM schemes, natural in every transporter. -/
def cmSmallLevelArithmeticStructure :
    schemes ⟶ (Functor.const (SmallCMLevel D)).obj base where
  app U := ((overTower).obj U).hom
  naturality {U V} k := by
    change ((overTower).map k).left ≫ ((overTower).obj V).hom =
      ((overTower).obj U).hom ≫ 𝟙 _
    simp

local notation "arithmeticStructure" => cmSmallLevelArithmeticStructure D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

/-- The generic base change is canonically the already constructed geometric CM tower.
Every component is the identity of its actual scheme fiber product. -/
def cmSmallLevelBaseChangeIso :
    RestrictedLevelTowerGalois.baseChangeTower F Fbar arithmeticStructure ≅
      geometricSchemes :=
  NatIso.ofComponents (fun U => Iso.refl _) (fun {U V} k => by
    apply pullback.hom_ext <;>
      simp [RestrictedLevelTowerGalois.baseChangeTower, cmGeometricSchemeTower,
        cmGeometricOverTower, cmGeometricFieldMap, cmSmallLevelArithmeticStructure,
        cmSchemeTower, representedCMSchemeTower])

local notation "baseChangeIso" => cmSmallLevelBaseChangeIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

/-- The base-field projection on the same geometric CM tower. -/
def cmSmallLevelArithmeticGeometricStructure :
    geometricSchemes ⟶ (Functor.const (SmallCMLevel D)).obj base :=
  projection ≫ arithmeticStructure

local notation "arithmeticGeometricStructure" => cmSmallLevelArithmeticGeometricStructure D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

/-- The composite to Spec F agrees with the geometric structure followed by Fbar over F. -/
theorem cmSmallLevelArithmeticGeometricStructure_eq :
    arithmeticGeometricStructure = geometricStructure ≫
      (Functor.const (SmallCMLevel D)).map (cmGeometricFieldMap (F := F)) := by
  apply NatTrans.ext
  funext U
  exact pullback.condition

/-- The comparison preserves the original first projections. -/
theorem cmSmallLevelBaseChangeIso_projection :
    (baseChangeIso).hom ≫ projection =
      RestrictedLevelTowerGalois.baseChangeProjection F Fbar arithmeticStructure := by
  apply NatTrans.ext
  funext U
  simp [cmSmallLevelBaseChangeIso, cmGeometricProjection,
    RestrictedLevelTowerGalois.baseChangeProjection, cmSmallLevelArithmeticStructure,
    cmGeometricFieldMap]

/-- Galois automorphisms of the actual geometric CM tower, via the constructed comparison. -/
def cmSmallLevelGaloisAut (σ : Gamma) : Aut geometricSchemes :=
  (baseChangeIso).symm ≪≫
    RestrictedLevelTowerGalois.towerGaloisAut arithmeticStructure σ ≪≫ baseChangeIso

local notation "galoisAut" => cmSmallLevelGaloisAut D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

/-- At each actual CM level the Galois map acts on the algebraic-closure factor. -/
@[simp] theorem cmSmallLevelGaloisAut_hom_app (σ : Gamma) (U : SmallCMLevel D) :
    (galoisAut σ).hom.app U =
      EtaleGaloisAction.baseChangeMap ((arithmeticStructure).app U) σ := by
  simp [cmSmallLevelGaloisAut, cmSmallLevelBaseChangeIso]
  exact Category.id_comp _

/-- The actual tower action, with the contravariant spectrum convention. -/
def cmSmallLevelGaloisAction : Gamma →* (Aut geometricSchemes)ᵐᵒᵖ where
  toFun σ := MulOpposite.op (galoisAut σ)
  map_one' := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    apply NatTrans.ext
    funext U
    change (galoisAut (1 : Gamma)).hom.app U = 𝟙 _
    rw [cmSmallLevelGaloisAut_hom_app]
    exact EtaleGaloisAction.baseChangeMap_one ((arithmeticStructure).app U)
  map_mul' σ τ := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    apply NatTrans.ext
    funext U
    simpa [Aut.Aut_mul_def] using
      (EtaleGaloisAction.baseChangeMap_comp ((arithmeticStructure).app U) σ τ).symm

local notation "galoisAction" => cmSmallLevelGaloisAction D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

/-- Every Galois automorphism is over the original base field. -/
theorem cmSmallLevelGaloisAction_over (σ : Gamma) :
    (galoisAction σ).unop.hom ≫ arithmeticGeometricStructure =
      arithmeticGeometricStructure := by
  apply NatTrans.ext
  funext U
  change (galoisAut σ).hom.app U ≫ _ ≫ _ = _ ≫ _
  rw [cmSmallLevelGaloisAut_hom_app, ← Category.assoc]
  change EtaleGaloisAction.baseChangeMap _ σ ≫ pullback.fst _ _ ≫ _ = _
  simp [EtaleGaloisAction.baseChangeMap, pullback.map,
    cmGeometricProjection, cmSmallLevelArithmeticStructure, cmGeometricFieldMap]


variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

local notation "towerEtale" => cmSmallLevelTowerEtale D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion
local notation "selfTrivial" => cmGeometricSchemeTower_restrictedSelfArrow D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q
local notation "galoisOver" => cmSmallLevelGaloisAction_over D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

variable (R : Type) [CommRing R]

local notation "coefficients" => cmSmallLevelCoefficientDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R
local notation "trivialCoefficients" => cmSmallLevelTrivialCoefficients D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

/-- Arithmetic base sheaves pulled back to every actual geometric CM level, with
constructed restriction/projection comparisons for the original transporters. -/
def cmSmallLevelArithmeticCoefficients (M : ModuleSheaf base R) : coefficients := by
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.canonicalCoefficients
    R arithmeticGeometricStructure M

local notation "arithmeticCoefficients" => cmSmallLevelArithmeticCoefficients D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

@[simp] theorem cmSmallLevelArithmeticCoefficients_obj (M : ModuleSheaf base R)
    (U : SmallCMLevel D) :
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    (arithmeticCoefficients M).obj (op U) =
      (EtaleInverseImage.inverseImage ((arithmeticGeometricStructure).app U) R).obj M := rfl

/-- The coefficient map uses the same geometric transporter and its actual base triangle. -/
theorem cmSmallLevelArithmeticCoefficients_map (M : ModuleSheaf base R)
    {U V : SmallCMLevel D} (k : U ⟶ V) :
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    (arithmeticCoefficients M).map k.op =
      (LevelTowerCohomology.restrictionProjectionIso R
        ((arithmeticGeometricStructure).app V) ((arithmeticGeometricStructure).app U)
        ((geometricSchemes).map k)
        (RestrictedLevelTowerGalois.structure_naturality arithmeticGeometricStructure k)).hom.app M := by
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  rfl

/-- The constructed arithmetic coefficients satisfy the full sheaf-level identity at
level elements, without an additional coefficient-triviality assumption. -/
theorem cmSmallLevelArithmeticCoefficients_trivial (M : ModuleSheaf base R) :
    trivialCoefficients (arithmeticCoefficients M) := by
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.isLevelTrivialCoefficients_canonical
    R selfTrivial M

/-- Pullback from Spec F is functorial in the base sheaf. -/
def cmSmallLevelArithmeticCoefficientsFunctor :
    ModuleSheaf base R ⥤ (trivialCoefficients).FullSubcategory := by
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.levelTrivialCanonicalCoefficientsFunctor
    R arithmeticGeometricStructure selfTrivial

local notation "arithmeticCoefficientFunctor" => cmSmallLevelArithmeticCoefficientsFunctor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

@[simp] theorem cmSmallLevelArithmeticCoefficientsFunctor_obj (M : ModuleSheaf base R) :
    ((arithmeticCoefficientFunctor).obj M).obj = arithmeticCoefficients M := rfl

@[simp] theorem cmSmallLevelArithmeticCoefficientsFunctor_map_app
    {M N : ModuleSheaf base R} (α : M ⟶ N) (U : SmallCMLevel D) :
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    (((arithmeticCoefficientFunctor).map α).hom).app (op U) =
      (EtaleInverseImage.inverseImage ((arithmeticGeometricStructure).app U) R).map α := rfl

/-- The underlying smooth finite-adelic cohomology of coefficients pulled back from Spec F. -/
def cmSmallLevelArithmeticCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤ SmoothRep.{0, 0, 0} R G := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothCanonicalCohomologyFunctor
    R arithmeticGeometricStructure selfTrivial d

local notation "arithmeticCohomologyFunctor" => cmSmallLevelArithmeticCohomologyFunctor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

/-- This is the same actual CM shrinking-level colimit with the constructed coefficients. -/
@[simp] theorem cmSmallLevelArithmeticCohomologyFunctor_obj (d : ℕ)
    (M : ModuleSheaf base R) :
    (arithmeticCohomologyFunctor d).obj M =
      cmSmallLevelSmoothCohomology D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R (arithmeticCoefficients M)
        (cmSmallLevelArithmeticCoefficients_trivial D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R M) d := rfl

/-- The commuting Galois action on the actual geometric CM cohomology, natural in
arithmetic base sheaves. The Galois group here has its algebraic group structure. -/
def cmSmallLevelGaloisCohomologyFunctor (d : ℕ) :
    ModuleSheaf base R ⥤ Action (SmoothRep.{0, 0, 0} R G) Gamma := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.automorphismActionFunctor
    R arithmeticGeometricStructure selfTrivial galoisAction galoisOver d

local notation "galoisCohomologyFunctor" => cmSmallLevelGaloisCohomologyFunctor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

@[simp] theorem cmSmallLevelGaloisCohomologyFunctor_obj_V (d : ℕ)
    (M : ModuleSheaf base R) :
    ((galoisCohomologyFunctor d).obj M).V = (arithmeticCohomologyFunctor d).obj M := rfl

/-- Forgetting Galois gives exactly the smooth actual CM cohomology functor. -/
def cmSmallLevelGaloisCohomologyForgetIso (d : ℕ) :
    galoisCohomologyFunctor d ⋙ Action.forget _ Gamma ≅
      arithmeticCohomologyFunctor d := Iso.refl _

/-- A Galois element acts by smooth pullback along its actual tower automorphism. -/
theorem cmSmallLevelGaloisCohomologyFunctor_ρ (d : ℕ) (M : ModuleSheaf base R)
    (σ : Gamma) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    ((galoisCohomologyFunctor d).obj M).ρ σ =
      (RestrictedLevelTowerCohomology.smoothCanonicalPullback
        R arithmeticGeometricStructure (galoisAction σ).unop.hom (galoisOver σ)
        selfTrivial selfTrivial d).app M := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  rfl

/-- At a level representative, Galois acts by the ordinary cohomological pullback and
the constructed projection-coefficient comparison at that same actual CM level. -/
theorem cmSmallLevelGaloisCohomology_ρ_ι_apply (d : ℕ) (M : ModuleSheaf base R)
    (σ : Gamma) (U : SmallCMLevel D)
    (x : (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) R d).obj
      ((EtaleInverseImage.inverseImage ((arithmeticGeometricStructure).app U) R).obj M)) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    SmoothRep.hom (((galoisCohomologyFunctor d).obj M).ρ σ)
        ((RestrictedLevelColimit.ι ((arithmeticCoefficients M).cohomology d) U).hom x) =
      (RestrictedLevelColimit.ι ((arithmeticCoefficients M).cohomology d) U).hom
        ((LevelTowerCohomology.projectionCohomologyMap R
          ((arithmeticGeometricStructure).app U) ((arithmeticGeometricStructure).app U)
          ((galoisAction σ).unop.hom.app U) (NatTrans.congr_app (galoisOver σ) U)
          d M).hom x) := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact congrArg (fun f => f.hom x)
    (RestrictedLevelTowerCohomology.canonicalPullback_ι R arithmeticGeometricStructure
      (galoisAction σ).unop.hom (galoisOver σ) M d U)

/-- The Galois and finite-adelic actions commute on the actual CM cohomology module. -/
theorem cmSmallLevelGaloisCohomology_commutes (d : ℕ) (M : ModuleSheaf base R)
    (σ : Gamma) (g : G) (x : ((galoisCohomologyFunctor d).obj M).V) :
    SmoothRep.hom (((galoisCohomologyFunctor d).obj M).ρ σ)
        (((galoisCohomologyFunctor d).obj M).V.obj.ρ g x) =
      ((galoisCohomologyFunctor d).obj M).V.obj.ρ g
        (SmoothRep.hom (((galoisCohomologyFunctor d).obj M).ρ σ) x) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom (((galoisCohomologyFunctor d).obj M).ρ σ)) g x

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
