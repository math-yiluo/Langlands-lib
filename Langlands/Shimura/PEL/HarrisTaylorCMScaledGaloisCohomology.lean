import Langlands.Shimura.PEL.HarrisTaylorCMLevelTransport
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCoefficients
import Langlands.Geometry.EtaleCoefficientEquivalence
import Langlands.Geometry.EtaleGeometricCoefficientReindex
import Langlands.Geometry.EtaleCoefficientDiagramPullback
import Langlands.Geometry.EtaleGeometricActionDiagram
import Langlands.Shimura.PEL.HarrisTaylorCMLambdaCohomology

/-! # Harris's coefficient systems on the geometric CM tower over scaled levels, with Galois action

The coefficient diagram `cmHarrisScaledCoefficientDiagram` of Harris's coefficient systems over
scaled levels and torsion stages lives on the CM schemes `X_U` over the reflex field. This module
pulls it back to the geometric levels `X̄_U = X_U ×_F F̄`, where the scheme maps are the tower maps
of the transporters composed with the Galois automorphisms `g_σ` of the field factor. Its
cohomology is a diagram of Galois actions over scaled levels and stages, and its limit over the
stages is the `ℓ`-power torsion limit of the cohomology with coefficients in `W`, as a functor of
the scaled level. See `HarrisTaylorCMScaledGaloisCohomology.md`.
-/

noncomputable section

universe wS wR uK uO uL uV

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-! ## Extension of scalars of Galois lattices as a functor -/

namespace Langlands.Shimura.LatticeGaloisRepresentation

variable {K : Type uK} [Field K] {O : Type uO} [CommRing O] {L : Type uL} [Field L]
  [Algebra O L]

/-- Extension of scalars `V ↦ L ⊗[O] V` of Galois actions on `O`-modules along `O → L`, as a
functor: on objects it is `baseChangeAction`, and an equivariant map `f` goes to `L ⊗ f`. -/
def baseChangeActionFunctor :
    Action (ModuleCat.{uV} O) (Field.absoluteGaloisGroup K) ⥤
      Action (ModuleCat.{max uL uV} L) (Field.absoluteGaloisGroup K) where
  obj V := baseChangeAction (L := L) V
  map {V V'} f :=
    { hom := ModuleCat.ofHom (f.hom.hom.baseChange L)
      comm := fun g => by
        apply ModuleCat.hom_ext
        change (f.hom.hom.baseChange L).comp ((V.ρ g).hom.baseChange L) =
          ((V'.ρ g).hom.baseChange L).comp (f.hom.hom.baseChange L)
        rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
        exact congrArg (fun t => LinearMap.baseChange L t)
          (congrArg ModuleCat.Hom.hom (f.comm g)) }
  map_id V := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp _ _

/-- The extension of scalars of an object is `baseChangeAction`. -/
@[simp] theorem baseChangeActionFunctor_obj (V : Action (ModuleCat.{uV} O)
    (Field.absoluteGaloisGroup K)) :
    (baseChangeActionFunctor (L := L)).obj V = baseChangeAction (L := L) V := rfl

/-- The extension of scalars of an equivariant map `f` is `L ⊗ f`. -/
theorem baseChangeActionFunctor_map_hom {V V' : Action (ModuleCat.{uV} O)
    (Field.absoluteGaloisGroup K)} (f : V ⟶ V') :
    ((baseChangeActionFunctor (L := L)).map f).hom.hom = f.hom.hom.baseChange L := rfl

end Langlands.Shimura.LatticeGaloisRepresentation

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open EtaleInverseImage EtaleGeometricDiagram
open Langlands.Global AdelicFunctoriality
open scoped CategoryTheory.Prod

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

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "projection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "galoisMap" => cmGeometricGaloisMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K] (p : Global.FinitePlace ℚ)
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)

local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "scaledSchemes" => cmScaledSchemeDiagram D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ

/-! ## The scheme diagrams over scaled levels, stages and Galois elements -/

/-- The index category: scaled levels, torsion stages and the Galois group. -/
abbrev CMScaledGaloisIndex := ((CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) × SingleObj Galois

/-- The arithmetic CM schemes over scaled levels, stages and Galois elements: the scheme diagram
`cmScaledSchemeDiagram` with the Galois factor ignored. -/
def cmScaledArithmeticGaloisSchemes : CMScaledGaloisIndex D p ρ ⥤ Scheme.{0}ᵒᵖ :=
  CategoryTheory.Prod.fst _ _ ⋙ scaledSchemes

/-- The geometric CM levels over scaled levels, stages and Galois elements. The arrow
`(f, σ)` gives the scheme map `g_σ ≫ T̄(f) : X̄_V ⟶ X̄_U`, the raw Galois map of `σ` followed by the
geometric tower map of the transporter of `f`. -/
def cmScaledGeometricGaloisSchemes : CMScaledGaloisIndex D p ρ ⥤ Scheme.{0}ᵒᵖ where
  obj i := op ((geometricSchemes).obj i.1.1.unop.level)
  map {i j} a := ((galoisMap a.2).app j.1.1.unop.level ≫
    (geometricSchemes).map (CMScaledLevel.Hom.hom a.1.1.unop)).op
  map_id i := by
    apply Quiver.Hom.unop_inj
    change (galoisMap (1 : Galois)).app i.1.1.unop.level ≫
      (geometricSchemes).map (𝟙 i.1.1.unop.level) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact cmGeometricGaloisMap_app_one D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q i.1.1.unop.level
  map_comp {i j k} a b := by
    apply Quiver.Hom.unop_inj
    change (galoisMap (@Mul.mul Galois _ b.2 a.2)).app k.1.1.unop.level ≫
        (geometricSchemes).map (CMScaledLevel.Hom.hom b.1.1.unop ≫
          CMScaledLevel.Hom.hom a.1.1.unop) =
      ((galoisMap b.2).app k.1.1.unop.level ≫
          (geometricSchemes).map (CMScaledLevel.Hom.hom b.1.1.unop)) ≫
        (galoisMap a.2).app j.1.1.unop.level ≫
          (geometricSchemes).map (CMScaledLevel.Hom.hom a.1.1.unop)
    rw [CategoryTheory.Functor.map_comp,
      show (galoisMap (@Mul.mul Galois _ b.2 a.2)).app k.1.1.unop.level =
          (galoisMap b.2).app k.1.1.unop.level ≫ (galoisMap a.2).app k.1.1.unop.level from
        (cmGeometricGaloisMap_app_mul D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q k.1.1.unop.level b.2 a.2).symm]
    simp only [Category.assoc]
    rw [(galoisMap a.2).naturality_assoc]

/-- The geometric projections `X̄_U ⟶ X_U` as a morphism of contravariant scheme diagrams. -/
def cmScaledGeometricGaloisProjection :
    cmScaledArithmeticGaloisSchemes D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q p ρ ⟶
      cmScaledGeometricGaloisSchemes D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q p ρ where
  app i := ((projection).app i.1.1.unop.level).op
  naturality {i j} a := by
    apply Quiver.Hom.unop_inj
    change (projection).app j.1.1.unop.level ≫
        (schemes).map (CMScaledLevel.Hom.hom a.1.1.unop) =
      ((galoisMap a.2).app j.1.1.unop.level ≫
          (geometricSchemes).map (CMScaledLevel.Hom.hom a.1.1.unop)) ≫
        (projection).app i.1.1.unop.level
    rw [Category.assoc, (projection).naturality,
      cmGeometricGaloisMap_app_projection_assoc]

local notation "arithmeticGaloisSchemes" => cmScaledArithmeticGaloisSchemes D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ
local notation "geometricGaloisSchemes" => cmScaledGeometricGaloisSchemes D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ
local notation "galoisProjection" => cmScaledGeometricGaloisProjection D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ

/-- The vertex `((X, k), σ)` of the geometric diagram is the geometric CM level of `X`. -/
@[simp] theorem cmScaledGeometricGaloisSchemes_obj (i : CMScaledGaloisIndex D p ρ) :
    ((geometricGaloisSchemes).obj i).unop = (geometricSchemes).obj i.1.1.unop.level := rfl

/-- The arrow `(f, σ)` gives `g_σ ≫ T̄(f)`. -/
theorem cmScaledGeometricGaloisSchemes_map {i j : CMScaledGaloisIndex D p ρ} (a : i ⟶ j) :
    ((geometricGaloisSchemes).map a).unop =
      (galoisMap a.2).app j.1.1.unop.level ≫
        (geometricSchemes).map (CMScaledLevel.Hom.hom a.1.1.unop) := rfl

/-- The vertex `((X, k), σ)` of the arithmetic diagram is the CM scheme of the level of `X`. -/
@[simp] theorem cmScaledArithmeticGaloisSchemes_obj (i : CMScaledGaloisIndex D p ρ) :
    ((arithmeticGaloisSchemes).obj i).unop = (schemes).obj i.1.1.unop.level := rfl

/-- The arrow `(f, σ)` of the arithmetic diagram gives the tower map of the transporter of `f`. -/
theorem cmScaledArithmeticGaloisSchemes_map {i j : CMScaledGaloisIndex D p ρ} (a : i ⟶ j) :
    ((arithmeticGaloisSchemes).map a).unop =
      (schemes).map (CMScaledLevel.Hom.hom a.1.1.unop) := rfl

/-- The components of the projection are the geometric projections `X̄_U ⟶ X_U`. -/
@[simp] theorem cmScaledGeometricGaloisProjection_app (i : CMScaledGaloisIndex D p ρ) :
    ((galoisProjection).app i).unop = (projection).app i.1.1.unop.level := rfl

/-! ## The coefficient diagram on the geometric levels -/

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "ℓ" => harrisCoefficientPrime p
local notation "hℓ" => harrisCoefficientPrime_ne_zero p
local notation "scaledCoefficients" => cmHarrisScaledCoefficientDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ

/-- Harris's coefficient systems over scaled levels, stages and Galois elements, on the CM schemes
over the reflex field: `cmHarrisScaledCoefficientDiagram`, converted to inverse-image coefficients
and reindexed along the projection forgetting the Galois factor. -/
def cmHarrisScaledArithmeticGaloisCoefficientDiagram :
    CoefficientDiagram Rcoeff (arithmeticGaloisSchemes) :=
  letI : ∀ {i j : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ} (a : i ⟶ j),
      Etale ((scaledSchemes).map a).unop := fun a =>
    cmScaledSchemeDiagram_etale D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor q existence geometry hRigid p ρ a
  (CoefficientDiagram.ofRestriction (scaledCoefficients)).reindex (CategoryTheory.Prod.fst _ _)

/-- Harris's coefficient systems over scaled levels, stages and Galois elements, on the geometric
CM levels: the inverse image of `cmHarrisScaledArithmeticGaloisCoefficientDiagram` along the
geometric projections. The vertex `((X, k), *)` is the inverse image to `X̄_U` of the stage-`k`
coefficient sheaf of `W` at the level `U` of `X`. -/
def cmHarrisScaledGeometricGaloisCoefficientDiagram :
    CoefficientDiagram Rcoeff (geometricGaloisSchemes) :=
  CoefficientDiagram.pullback Rcoeff (galoisProjection)
    (cmHarrisScaledArithmeticGaloisCoefficientDiagram D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q p ρ existence geometry hRigid)

local notation "galoisCoefficients" => cmHarrisScaledGeometricGaloisCoefficientDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q p ρ existence
  geometry hRigid

/-- The vertex `((X, k), σ)` is the inverse image to the geometric level of the stage-`k`
coefficient sheaf at the level of `X`. -/
@[simp] theorem cmHarrisScaledGeometricGaloisCoefficientDiagram_obj
    (i : CMScaledGaloisIndex D p ρ) :
    (galoisCoefficients).obj i =
      (inverseImage ((projection).app i.1.1.unop.level) Rcoeff).obj
        ((cmHarrisCoefficientSystem D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q i.1.1.unop.level ρ p ℓ hℓ existence
          geometry (hRigid i.1.1.unop.level)).obj i.1.2) := rfl

/-! ## Cohomology with Galois actions and its torsion limit -/

variable [∀ U : SmallCMLevel D, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

instance cmScaledGeometricGaloisSchemes_hasDerivedCategory (x : CMScaledGaloisIndex D p ρ) :
    HasDerivedCategory.{wS}
      (EtaleDerivedSections.ModuleSheaf ((geometricGaloisSchemes).obj x).unop Rcoeff) :=
  inferInstanceAs (HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((geometricSchemes).obj x.1.1.unop.level) Rcoeff))

/-- The cohomology of degree `degree` of the geometric CM levels with coefficients in the stages
of `W`, as a diagram over scaled levels and stages of actions of `Gal(F̄/F)`. -/
def cmHarrisScaledGaloisCohomologyAction (degree : ℕ) :
    ((CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) ⥤ Action (ModuleCat.{0} Rcoeff) Galois :=
  (galoisCoefficients).cohomologyAction degree

local notation "scaledCohomologyAction" => cmHarrisScaledGaloisCohomologyAction D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q p ρ existence
  geometry hRigid

/-- At the scaled level `X` and stage `k`, the underlying module is the cohomology
`H^d(X̄_U, W_k)` of the geometric level `U` of `X` with coefficients in the inverse image of the
stage-`k` coefficient sheaf at `U`. -/
theorem cmHarrisScaledGaloisCohomologyAction_obj_V (degree : ℕ)
    (x : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) :
    (((scaledCohomologyAction) degree).obj x).V =
      (EtaleDerivedSections.cohomology ((geometricSchemes).obj x.1.unop.level) Rcoeff
        degree).obj ((inverseImage ((projection).app x.1.unop.level) Rcoeff).obj
          ((cmHarrisCoefficientSystem D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor q x.1.unop.level ρ p ℓ hℓ existence
            geometry (hRigid x.1.unop.level)).obj x.2)) :=
  CoefficientDiagram.cohomologyAction_obj_V (galoisCoefficients) degree x

/-- The `ℓ`-power torsion limit `lim_k H^d(X̄_U, W_k)` of the cohomology with coefficients in the
stages of `W`, as a functor of the scaled level with values in actions of `Gal(F̄/F)`. -/
def cmHarrisScaledAdicCohomology (degree : ℕ) :
    (CMScaledLevel D ρ p)ᵒᵖ ⥤ Action (ModuleCat.{0} Rcoeff) Galois :=
  Functor.curry.obj ((scaledCohomologyAction) degree) ⋙ lim

local notation "scaledAdic" => cmHarrisScaledAdicCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q p ρ existence geometry hRigid

/-- At a scaled level `X`, the torsion limit is the limit over the stages. -/
theorem cmHarrisScaledAdicCohomology_obj (degree : ℕ) (X : (CMScaledLevel D ρ p)ᵒᵖ) :
    ((scaledAdic) degree).obj X =
      limit ((Functor.curry.obj ((scaledCohomologyAction) degree)).obj X) := rfl

/-- The `λ`-adic cohomology `K_λ ⊗ lim_k H^d(X̄_U, W_k)` as a functor of the scaled level, with
values in actions of `Gal(F̄/F)` on `K_λ`-vector spaces. -/
def cmHarrisScaledLambdaCohomology (l : FinitePlacesAbove K p) (degree : ℕ) :
    (CMScaledLevel D ρ p)ᵒᵖ ⥤
      Action (ModuleCat.{0} (FiniteCompletion K l.1)) (Field.absoluteGaloisGroup F) :=
  letI := harrisCoefficientComponentAlgebra K p l
  (scaledAdic) degree ⋙
    LatticeGaloisRepresentation.baseChangeActionFunctor (L := FiniteCompletion K l.1)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
