import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCoefficients
import Mathlib.CategoryTheory.Action.Basic

/-! # Original geometric CM coefficients as a Galois diagram -/

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem combineCoefficientTransitions
    {V : Type u} {J : Type v} [Category.{w} V] [Category.{z} J]
    (S : J ⥤ V) (I₁ I₂ I₃ : V ⥤ V)
    (c₁ : S ⋙ I₁ ⟶ S) (c₂ : S ⋙ I₂ ⟶ S) (c₃ : S ⋙ I₃ ⟶ S)
    (t : I₁ ⋙ I₂ ⟶ I₃) {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (hc : I₂.map (c₁.app i) ≫ c₂.app i = t.app (S.obj i) ≫ c₃.app i) :
    t.app (S.obj i) ≫ (c₃.app i ≫ S.map (a ≫ b)) =
      I₂.map (c₁.app i ≫ S.map a) ≫ (c₂.app j ≫ S.map b) := by
  calc
    _ = (I₂.map (c₁.app i) ≫ c₂.app i) ≫ (S.map a ≫ S.map b) := by
      rw [S.map_comp]
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (S.map a ≫ S.map b)) hc.symm
    _ = _ := by
      simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map,
        Category.assoc] using congrArg
        (fun z => I₂.map (c₁.app i) ≫ z ≫ S.map b) (c₂.naturality a).symm

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Cohomology Langlands.Geometry
open EtaleInverseImage EtaleGeometricDiagram
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

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "overTower" => representedCMOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor chosen
local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "geometricOver" => cmGeometricOverTower D C preservation composition
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

variable (U : SmallCMLevel D)

local notation "Galois" => (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
local notation "g" σ:max => (galoisMap σ).app U

/-- The fixed geometric CM level, indexed by exponents and raw Galois
comorphisms. Its scheme arrows have the opposite variance. -/
def cmGeometricGaloisCoefficientSchemes :
    (ℕᵒᵖ × SingleObj Galois) ⥤ Scheme.{0}ᵒᵖ where
  obj _ := op ((geometricSchemes).obj U)
  map a := (g a.2).op
  map_id _ := by
    change (g (1 : Galois)).op = (𝟙 _).op
    exact congrArg Quiver.Hom.op
      (cmGeometricGaloisMap_app_one D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U)
  map_comp a b := by
    change (g (@Mul.mul Galois _ b.2 a.2)).op = (g a.2).op ≫ (g b.2).op
    exact congrArg Quiver.Hom.op
      (cmGeometricGaloisMap_app_mul D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q U b.2 a.2).symm

local notation "coefficientSchemes" => cmGeometricGaloisCoefficientSchemes D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U

/-- Every index vertex is the unchanged original geometric CM scheme. -/
@[simp] theorem cmGeometricGaloisCoefficientSchemes_obj
    (i : ℕᵒᵖ × SingleObj Galois) :
    ((coefficientSchemes).obj i).unop = (geometricSchemes).obj U := rfl

/-- The scheme map is precisely the raw spectrum-comorphism action,
independent of the exponent arrow. -/
@[simp] theorem cmGeometricGaloisCoefficientSchemes_map
    {i j : ℕᵒᵖ × SingleObj Galois} (a : i ⟶ j) :
    ((coefficientSchemes).map a).unop = g a.2 := rfl

variable [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "Rcoeff" => HarrisCoefficientIntegers K p
local notation "Pcoeff" => inverseImage π Rcoeff
local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "divisible" => cmHarrisCoefficientDivisibleSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "geometricSystem" => cmHarrisGeometricCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "geometricDivisible" => cmHarrisGeometricCoefficientDivisibleSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "Ccoeff" => cmGeometricGaloisInverseImageIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U Rcoeff

local notation "coefficientIso" => cmHarrisGeometricCoefficientGaloisIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The original geometric torsion sheaves, reductions and constructed raw
Galois comparisons form a genuine geometric coefficient diagram. -/
def cmHarrisGeometricGaloisCoefficientDiagram :
    CoefficientDiagram Rcoeff coefficientSchemes where
  obj i := (geometricSystem).obj i.1
  map {i j} a := ((coefficientIso) a.2).hom.app i.1 ≫ (geometricSystem).map a.1
  map_id i := by
    change ((coefficientIso) 1).hom.app i.1 ≫ (geometricSystem).map (𝟙 i.1) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact cmHarrisGeometricCoefficientGaloisIso_one D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid i.1
  map_comp {i j k} a b := by
    have hc := cmHarrisGeometricCoefficientGaloisIso_mul D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid b.2 a.2 i.1
    apply combineCoefficientTransitions (geometricSystem)
      (inverseImage (g a.2) Rcoeff) (inverseImage (g b.2) Rcoeff)
      (diagramInverseImage Rcoeff coefficientSchemes (a ≫ b))
      (((coefficientIso) a.2).hom) (((coefficientIso) b.2).hom)
      (((coefficientIso) (a ≫ b).2).hom)
      ((diagramInverseImageComp Rcoeff coefficientSchemes a b).hom) a.1 b.1
    simpa only [diagramInverseImageComp, cmGeometricGaloisCoefficientSchemes,
      Iso.trans_hom, NatTrans.comp_app, Quiver.Hom.unop_op,
      CategoryTheory.prod_comp_snd, SingleObj.comp_as_mul, Category.assoc] using hc

local notation "galoisCoefficients" => cmHarrisGeometricGaloisCoefficientDiagram D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Every vertex is the specified original geometric coefficient sheaf. -/
@[simp] theorem cmHarrisGeometricGaloisCoefficientDiagram_obj
    (i : ℕᵒᵖ × SingleObj Galois) :
    (galoisCoefficients).obj i = (geometricSystem).obj i.1 := rfl

/-- Every combined transition is the constructed Galois comparison followed
by the unchanged original coefficient reduction. -/
theorem cmHarrisGeometricGaloisCoefficientDiagram_map
    {i j : ℕᵒᵖ × SingleObj Galois} (a : i ⟶ j) :
    (galoisCoefficients).map a =
      ((coefficientIso) a.2).hom.app i.1 ≫ (geometricSystem).map a.1 := rfl

/-- A pure Galois arrow uses exactly the original finite-stage comparison. -/
@[simp] theorem cmHarrisGeometricGaloisCoefficientDiagram_galois
    (r : ℕᵒᵖ) (σ : Galois) :
    (galoisCoefficients).map (𝟙 r ×ₘ σ : (r, SingleObj.star Galois) ⟶ (r, SingleObj.star Galois)) = ((coefficientIso) σ).hom.app r := by
  change ((coefficientIso) σ).hom.app r ≫ (geometricSystem).map (𝟙 r) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- A pure reduction retains the canonical inverse-image unit comparison
and the exact original geometric reduction. -/
theorem cmHarrisGeometricGaloisCoefficientDiagram_reduction
    {r s : ℕᵒᵖ} (f : r ⟶ s) :
    (galoisCoefficients).map (f ×ₘ (1 : Galois) :
      (r, SingleObj.star Galois) ⟶ (s, SingleObj.star Galois)) =
      (diagramInverseImageId Rcoeff coefficientSchemes
        (r, SingleObj.star Galois)).hom.app ((geometricSystem).obj r) ≫
          (geometricSystem).map f := by
  change ((coefficientIso) 1).hom.app r ≫ (geometricSystem).map f = _
  rw [cmHarrisGeometricCoefficientGaloisIso_one]
  rfl

/-- The normalized original divisible-system inclusions commute with the
pure Galois transitions of this coefficient diagram. -/
theorem cmHarrisGeometricGaloisCoefficientDiagram_inclusion
    (σ : Galois) {r s : ℕ} (hrs : r < s) :
    (inverseImage (g σ) Rcoeff).map ((geometricDivisible).inclusion hrs) ≫
        (galoisCoefficients).map (𝟙 (op s) ×ₘ σ :
          (op s, SingleObj.star Galois) ⟶ (op s, SingleObj.star Galois)) =
      (galoisCoefficients).map (𝟙 (op r) ×ₘ σ :
          (op r, SingleObj.star Galois) ⟶ (op r, SingleObj.star Galois)) ≫
        (geometricDivisible).inclusion hrs := by
  simp only [cmHarrisGeometricGaloisCoefficientDiagram_galois]
  exact cmHarrisGeometricCoefficientGaloisIso_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid σ hrs

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
