import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientDiagram
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSheaf

/-! # Original CM coefficient covers as an equivariant exponent diagram -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients

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

local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "quotientAction" => cmNormalQuotientAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "refinement" => cmNormalRefinement D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

local notation "levels" => cmHarrisCoefficientLevels D ρ p U m hm
local notation "groups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "Vcoeff" k => cmHarrisCoefficientLevel D ρ p U m hm k
local notation "hcoeff" k => cmHarrisCoefficientLevel_le D ρ p U m hm k
set_option quotPrecheck false in
local notation "hincl" f => cmHarrisCoefficientLevel_antitone D ρ p U m hm (leOfHom (f).unop)
local notation "X" => Functor.obj (schemes q) U

/-- The original chosen scheme tower at the actual full coefficient kernel levels. -/
def cmHarrisCoefficientSchemeDiagram : EquivariantDiagram groups Scheme where
  obj := levels ⋙ schemes q
  ρ k := (quotientAction U (Vcoeff k.unop) (hcoeff k.unop) q).ρ
  comm {i j} f g :=
    (refinement U (Vcoeff j.unop) (Vcoeff i.unop) (hcoeff j.unop) (hincl f) q).comm g

local notation "schemeDiagram" => cmHarrisCoefficientSchemeDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm

/-- The underlying diagram uses precisely the existing CM scheme tower. -/
@[simp] theorem cmHarrisCoefficientSchemeDiagram_obj :
    (schemeDiagram).obj = levels ⋙ schemes q := rfl

/-- Every transition is the original identity-transporter forgetting map. -/
@[simp] theorem cmHarrisCoefficientSchemeDiagram_map {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (schemeDiagram).obj.map f = (schemes q).map (smallCMInclusion D (hincl f)) := rfl

/-- Its transition is precisely the existing equivariant normal refinement. -/
@[simp] theorem cmHarrisCoefficientSchemeDiagram_map_refinement
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (schemeDiagram).obj.map f =
      (refinement U (Vcoeff j.unop) (Vcoeff i.unop) (hcoeff j.unop) (hincl f) q).hom :=
  rfl

/-- Every transition preserves the original structure morphism to the same CM field. -/
theorem cmHarrisCoefficientSchemeDiagram_map_over {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (schemeDiagram).obj.map f ≫ ((chosen q) (Vcoeff j.unop)).base.obj.hom =
      ((chosen q) (Vcoeff i.unop)).base.obj.hom :=
  representedCMNormalRefinement_over D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosen q) U (Vcoeff j.unop)
    (Vcoeff i.unop) (hcoeff j.unop) (hincl f)

/-- On representatives the residual action is the original inverse-right transporter. -/
@[simp] theorem cmHarrisCoefficientSchemeDiagram_action_mk (k : ℕᵒᵖ)
    (g : U.obj.subgroup) :
    (schemeDiagram).ρ k (QuotientGroup.mk g) =
      (schemes q).map (smallCMNormalInverseArrow D U (Vcoeff k.unop) (hcoeff k.unop) g) := rfl

/-- All coefficient levels project naturally to the same original coarse CM scheme. -/
def cmHarrisCoefficientSchemeProjection :
    (schemeDiagram).obj ⟶ (Functor.const ℕᵒᵖ).obj X where
  app k := (schemes q).map (smallCMInclusion D (hcoeff k.unop))
  naturality i j f := by
    dsimp [cmHarrisCoefficientSchemeDiagram, cmHarrisCoefficientLevels]
    rw [Category.comp_id, ← (schemes q).map_comp, smallCMInclusion_trans]

local notation "projection" => cmHarrisCoefficientSchemeProjection D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm

/-- The projection at an index is exactly the original coefficient-level forgetting. -/
@[simp] theorem cmHarrisCoefficientSchemeProjection_app (k : ℕᵒᵖ) :
    (projection).app k = (schemes q).map (smallCMInclusion D (hcoeff k.unop)) := rfl

/-- The coarse projections also preserve the original CM-field structure morphisms. -/
theorem cmHarrisCoefficientSchemeProjection_over (k : ℕᵒᵖ) :
    (projection).app k ≫ ((chosen q) U).base.obj.hom =
      ((chosen q) (Vcoeff k.unop)).base.obj.hom :=
  representedCMSchemeTower_over D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosen q) (smallCMInclusion D (hcoeff k.unop))

/-- The original residual actions preserve these original coarse projections. -/
@[reassoc] theorem cmHarrisCoefficientSchemeProjection_invariant (k : ℕᵒᵖ)
    (g : (groups).obj k) :
    (schemeDiagram).ρ k g ≫ (projection).app k = (projection).app k :=
  representedCMNormalProjection_invariant D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (chosen q) U (Vcoeff k.unop) (hcoeff k.unop) g

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "torsor" k => cmHarrisCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

/-- The original coefficient covers and forgetting maps form a functor in the actual
small etale category of the original coarse scheme. -/
def cmHarrisCoefficientEtaleTower : ℕᵒᵖ ⥤ (X).Etale where
  obj k := (torsor k.unop).val.V
  map {i j} f := MorphismProperty.Over.homMk ((schemeDiagram).obj.map f) (by
    change (schemeDiagram).obj.map f ≫ (projection).app j = (projection).app i
    have e := (projection).naturality f
    change (schemeDiagram).obj.map f ≫ (projection).app j =
      (projection).app i ≫ 𝟙 X at e
    exact e.trans (Category.comp_id _))
  map_id k := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).obj.map_id k
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).obj.map_comp f g

local notation "etaleTower" => cmHarrisCoefficientEtaleTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The finite geometric torsor actions form one equivariant diagram over the exact
original residual group diagram. -/
def cmHarrisCoefficientEtaleDiagram : EquivariantDiagram groups (X).Etale where
  obj := etaleTower
  ρ k := (torsor k.unop).val.ρ
  comm f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (schemeDiagram).comm f g

local notation "etaleDiagram" => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Every action in the diagram is exactly the previously constructed original torsor. -/
@[simp] theorem cmHarrisCoefficientEtaleDiagram_action (k : ℕᵒᵖ) :
    (etaleDiagram).action k = (torsor k.unop).val := rfl

/-- The source of each small-etale object is exactly the original coefficient-level scheme. -/
@[simp] theorem cmHarrisCoefficientEtaleDiagram_obj_left (k : ℕᵒᵖ) :
    ((etaleDiagram).obj.obj k).left = (schemes q).obj (Vcoeff k.unop) := rfl

/-- Its finite geometric torsor property is derived from the same named premises. -/
theorem cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor (k : ℕᵒᵖ) :
    IsFiniteGeometricTorsor X ((etaleDiagram).action k) :=
  (torsor k.unop).property

/-- Each original coefficient cover covers the final object of the same small-etale site. -/
theorem cmHarrisCoefficientEtaleDiagram_coversTop (k : ℕᵒᵖ) :
    (Scheme.smallEtaleTopology X).CoversTop (fun _ : Unit => (etaleDiagram).obj.obj k) :=
  cmHarrisCoefficientTorsor_coversTop D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U existence geometry hRigid ρ p m hm k.unop

/-- Each small-etale transition has exactly the original scheme forgetting map. -/
@[simp] theorem cmHarrisCoefficientEtaleDiagram_map_left {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((etaleDiagram).obj.map f).left =
      (schemes q).map (smallCMInclusion D (hincl f)) := rfl

/-- The etale action retains the same inverse-right deck normalization on representatives. -/
@[simp] theorem cmHarrisCoefficientEtaleDiagram_action_mk_left (k : ℕᵒᵖ)
    (g : U.obj.subgroup) :
    ((etaleDiagram).ρ k (QuotientGroup.mk g)).left =
      (schemes q).map (smallCMNormalInverseArrow D U (Vcoeff k.unop) (hcoeff k.unop) g) := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
