import Langlands.Shimura.PEL.HarrisTaylorCMGeometricGalois
import Langlands.Geometry.EtaleGeometricCoefficientDiagram

/-! # Coherent Galois inverse images of the original geometric CM coefficients -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Cohomology Langlands.Geometry
open EtaleInverseImage

private theorem inverseImageCongr_trans_app {X Z : Scheme.{0}}
    (R : Type) [CommRing R] {f g k : Z ⟶ X} (e : f = g) (e' : g = k)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{0} R)) :
    (inverseImageCongr R e).hom.app M ≫ (inverseImageCongr R e').hom.app M =
      (inverseImageCongr R (e.trans e')).hom.app M := by
  subst g
  subst k
  simp

private theorem inverseImageComp_congr_left_app {X Z V : Scheme.{0}}
    (R : Type) [CommRing R] {f f' : Z ⟶ X} (e : f = f') (g : V ⟶ Z)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{0} R)) :
    (inverseImage g R).map ((inverseImageCongr R e).hom.app M) ≫
        (inverseImageComp R f' g).hom.app M =
      (inverseImageComp R f g).hom.app M ≫
        (inverseImageCongr R (congrArg (fun k => g ≫ k) e)).hom.app M := by
  subst f'
  simp

private theorem inverseImageComp_congr_right_app {X Z V : Scheme.{0}}
    (R : Type) [CommRing R] (f : Z ⟶ X) {g g' : V ⟶ Z} (e : g = g')
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{0} R)) :
    (inverseImageCongr R e).hom.app ((inverseImage f R).obj M) ≫
        (inverseImageComp R f g').hom.app M =
      (inverseImageComp R f g).hom.app M ≫
        (inverseImageCongr R (congrArg (fun k => k ≫ f) e)).hom.app M := by
  subst g'
  simp

private def fixedProjectionInverseImageIso {X Z : Scheme.{0}}
    (R : Type) [CommRing R] (π : Z ⟶ X) (g : Z ⟶ Z) (e : g ≫ π = π) :
    inverseImage π R ⋙ inverseImage g R ≅ inverseImage π R :=
  inverseImageComp R π g ≪≫ inverseImageCongr R e

private theorem fixedProjectionInverseImageIso_one {X Z : Scheme.{0}}
    (R : Type) [CommRing R] (π : Z ⟶ X) (g : Z ⟶ Z)
    (eg : g ≫ π = π) (e1 : g = 𝟙 Z)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{0} R)) :
    (fixedProjectionInverseImageIso R π g eg).hom.app M =
      (inverseImageCongr R e1).hom.app ((inverseImage π R).obj M) ≫
        (inverseImageId R Z).hom.app ((inverseImage π R).obj M) := by
  subst g
  have hi := congrArg (fun t => t.app M) (inverseImageComp_id_source R π)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app] at hi
  replace hi := hi.trans (Category.comp_id _)
  simpa only [fixedProjectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app,
    inverseImageCongr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp] using hi

private theorem fixedProjectionInverseImageIso_comp {X Z : Scheme.{0}}
    (R : Type) [CommRing R] (π : Z ⟶ X) (g h k : Z ⟶ Z)
    (eg : g ≫ π = π) (eh : h ≫ π = π) (ek : k ≫ π = π)
    (egh : g ≫ h = k) (M : Sheaf X.smallEtaleTopology (ModuleCat.{0} R)) :
    (inverseImage g R).map ((fixedProjectionInverseImageIso R π h eh).hom.app M) ≫
        (fixedProjectionInverseImageIso R π g eg).hom.app M =
      (inverseImageComp R h g).hom.app ((inverseImage π R).obj M) ≫
        (inverseImageCongr R egh).hom.app ((inverseImage π R).obj M) ≫
        (fixedProjectionInverseImageIso R π k ek).hom.app M := by
  have ha := congrArg (fun t => t.app M) (inverseImageComp_assoc R π h g)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at ha
  dsimp only [fixedProjectionInverseImageIso, Iso.trans_hom, NatTrans.comp_app]
  calc
    _ = (inverseImage g R).map ((inverseImageComp R π h).hom.app M) ≫
        ((inverseImage g R).map ((inverseImageCongr R eh).hom.app M) ≫
          (inverseImageComp R π g).hom.app M) ≫
            (inverseImageCongr R eg).hom.app M := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (inverseImage g R).map ((inverseImageComp R π h).hom.app M) ≫
        ((inverseImageComp R (h ≫ π) g).hom.app M ≫
          (inverseImageCongr R (congrArg (fun t => g ≫ t) eh)).hom.app M) ≫
            (inverseImageCongr R eg).hom.app M := by
      rw [inverseImageComp_congr_left_app R eh g M]
    _ = ((inverseImage g R).map ((inverseImageComp R π h).hom.app M) ≫
          (inverseImageComp R (h ≫ π) g).hom.app M) ≫
        (inverseImageCongr R (congrArg (fun t => g ≫ t) eh)).hom.app M ≫
          (inverseImageCongr R eg).hom.app M := by simp only [Category.assoc]
    _ = _ := by
      rw [ha]
      simp only [Category.assoc]
      rw [← Category.assoc ((inverseImageCongr R egh).hom.app _)
        ((inverseImageComp R π k).hom.app M),
        inverseImageComp_congr_right_app R π egh M]
      simp only [Category.assoc]
      rw [inverseImageCongr_trans_app, inverseImageCongr_trans_app,
        inverseImageCongr_trans_app]

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

variable (U : SmallCMLevel D) (R : Type) [CommRing R]

local notation "π" => (projection).app U
local notation "P" => inverseImage π R
local notation "g" σ:max => (galoisMap σ).app U

/-- Canonical inverse image along the actual Galois map preserves every original
coefficient sheaf pulled back along the geometric projection. -/
def cmGeometricGaloisInverseImageIso (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    P ⋙ inverseImage (g σ) R ≅ P :=
  fixedProjectionInverseImageIso R π (g σ)
    (cmGeometricGaloisMap_app_projection D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q σ U)

local notation "Ciso" => cmGeometricGaloisInverseImageIso D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U R

/-- The unit is the specified inverse-image identity comparison, with equality
transport of the proved geometric identity retained. -/
theorem cmGeometricGaloisInverseImageIso_one
    (M : Sheaf ((schemes).obj U).smallEtaleTopology (ModuleCat.{0} R)) :
    ((Ciso) 1).hom.app M =
      (inverseImageCongr R (show g (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) =
        𝟙 _ from congrArg (fun t => t.app U)
          (cmGeometricGaloisMap_one D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor q))).hom.app
              ((P).obj M) ≫
        (inverseImageId R ((geometricSchemes).obj U)).hom.app ((P).obj M) := by
  exact fixedProjectionInverseImageIso_one R π (g 1) _ _ M

/-- The constructed maps satisfy the raw Galois cocycle, with the actual
composition and equality comparisons of inverse image. -/
theorem cmGeometricGaloisInverseImageIso_mul
    (σ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (M : Sheaf ((schemes).obj U).smallEtaleTopology (ModuleCat.{0} R)) :
    (inverseImage (g σ) R).map (((Ciso) τ).hom.app M) ≫ ((Ciso) σ).hom.app M =
      (inverseImageComp R (g τ) (g σ)).hom.app ((P).obj M) ≫
        (inverseImageCongr R (show g σ ≫ g τ = g (σ * τ) from
          (congrArg (fun t => t.app U)
            (cmGeometricGaloisMap_mul D C preservation composition unitCoherence
              associativity comparison symmetry stability square universality
              dualityNaturality polarizationStability compatibility h htor q σ τ)).symm)).hom.app
                ((P).obj M) ≫ ((Ciso) (σ * τ)).hom.app M :=
  fixedProjectionInverseImageIso_comp R π (g σ) (g τ) (g (σ * τ)) _ _ _ _ M

omit [CommRing R] in
/-- The actual raw component identity used in the coefficient unit comparison. -/
theorem cmGeometricGaloisMap_app_one :
    (galoisMap (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)).app U = 𝟙 _ :=
  congrArg (fun t => t.app U)
    (cmGeometricGaloisMap_one D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q)

omit [CommRing R] in
/-- The actual raw component composition used in the coefficient cocycle. -/
theorem cmGeometricGaloisMap_app_mul
    (σ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    (galoisMap σ).app U ≫ (galoisMap τ).app U = (galoisMap (σ * τ)).app U :=
  (congrArg (fun t => t.app U)
    (cmGeometricGaloisMap_mul D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q σ τ)).symm

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

/-- The whole original geometric coefficient diagram is canonically identified
with its inverse image along each constructed raw Galois map. -/
def cmHarrisGeometricCoefficientGaloisIso
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    geometricSystem ⋙ inverseImage (g σ) Rcoeff ≅ geometricSystem :=
  Functor.associator system Pcoeff (inverseImage (g σ) Rcoeff) ≪≫
    Functor.isoWhiskerLeft system ((Ccoeff) σ)

local notation "coefficientIso" => cmHarrisGeometricCoefficientGaloisIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- At each exponent the comparison is exactly the canonical comparison
applied to the specified original sheaf. -/
@[simp] theorem cmHarrisGeometricCoefficientGaloisIso_hom_app
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (r : ℕᵒᵖ) :
    ((coefficientIso) σ).hom.app r = ((Ccoeff) σ).hom.app ((system).obj r) := by
  simp only [cmHarrisGeometricCoefficientGaloisIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  exact Category.id_comp _

/-- Naturality retains every specified original reduction on the geometric diagram. -/
theorem cmHarrisGeometricCoefficientGaloisIso_reduction
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) {r s : ℕᵒᵖ} (f : r ⟶ s) :
    (inverseImage (g σ) Rcoeff).map ((geometricSystem).map f) ≫
        ((coefficientIso) σ).hom.app s =
      ((coefficientIso) σ).hom.app r ≫ (geometricSystem).map f :=
  ((coefficientIso) σ).hom.naturality f

/-- The same comparison intertwines the original normalized inclusions
transported to the actual geometric sheaves. -/
theorem cmHarrisGeometricCoefficientGaloisIso_inclusion
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) {r s : ℕ} (hrs : r < s) :
    (inverseImage (g σ) Rcoeff).map ((geometricDivisible).inclusion hrs) ≫
        ((coefficientIso) σ).hom.app (op s) =
      ((coefficientIso) σ).hom.app (op r) ≫ (geometricDivisible).inclusion hrs := by
  simpa only [cmHarrisGeometricCoefficientGaloisIso_hom_app,
    cmHarrisGeometricCoefficientDivisibleSystem_inclusion,
    cmHarrisCoefficientDivisibleSystem_tower,
    cmHarrisGeometricCoefficientDivisibleSystem_tower,
    cmHarrisGeometricCoefficientSystem, Functor.comp_obj, Functor.comp_map] using
      ((Ccoeff) σ).hom.naturality ((divisible).inclusion hrs)

/-- Every finite stage satisfies the canonical unit law. -/
theorem cmHarrisGeometricCoefficientGaloisIso_one (r : ℕᵒᵖ) :
    ((coefficientIso) 1).hom.app r =
      (inverseImageCongr Rcoeff
        (cmGeometricGaloisMap_app_one D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U)).hom.app
            ((geometricSystem).obj r) ≫
        (inverseImageId Rcoeff ((geometricSchemes).obj U)).hom.app
          ((geometricSystem).obj r) := by
  rw [cmHarrisGeometricCoefficientGaloisIso_hom_app]
  exact cmGeometricGaloisInverseImageIso_one D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U Rcoeff ((system).obj r)

/-- Every finite stage satisfies the raw Galois cocycle with the specified
inverse-image composition and base-map equality comparisons. -/
theorem cmHarrisGeometricCoefficientGaloisIso_mul
    (σ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (r : ℕᵒᵖ) :
    (inverseImage (g σ) Rcoeff).map (((coefficientIso) τ).hom.app r) ≫
        ((coefficientIso) σ).hom.app r =
      (inverseImageComp Rcoeff (g τ) (g σ)).hom.app ((geometricSystem).obj r) ≫
        (inverseImageCongr Rcoeff
          (cmGeometricGaloisMap_app_mul D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality
            dualityNaturality polarizationStability compatibility h htor q U σ τ)).hom.app
              ((geometricSystem).obj r) ≫ ((coefficientIso) (σ * τ)).hom.app r := by
  simp only [cmHarrisGeometricCoefficientGaloisIso_hom_app]
  exact cmGeometricGaloisInverseImageIso_mul D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U Rcoeff σ τ ((system).obj r)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
