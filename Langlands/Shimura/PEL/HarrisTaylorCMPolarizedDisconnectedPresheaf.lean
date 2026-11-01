import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedUnpointedPresheaf
import Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes

/-! # The actual disconnected normalized CM polarized tower presheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

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

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "admissible" => AdmissibleCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

/-- An actual connected open component with its restricted CM structure map. -/
def componentCMOver (X : Over (Spec (.of F))) [IsLocallyNoetherian X.left]
    (c : _root_.ConnectedComponents X.left) : Over (Spec (.of F)) :=
  Over.mk (componentι X.left c ≫ X.hom)

/-- Named prerequisites on each actual connected component of a locally
Noetherian CM base. No connectedness of the original base is required. -/
structure ComponentwiseAdmissibleCMBase (X : Over (Spec (.of F))) : Prop where
  locallyNoetherian : IsLocallyNoetherian X.left
  components : letI := locallyNoetherian
    ∀ c : _root_.ConnectedComponents X.left,
      admissible (componentCMOver X c)

/-- Every actual over-category morphism between these bases is retained. -/
abbrev ComponentwiseAdmissibleCMBaseCategory :=
  ObjectProperty.FullSubcategory
    (ComponentwiseAdmissibleCMBase D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality)

local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality

instance componentwiseCMBaseLocallyNoetherian (X : DisBases) :
    IsLocallyNoetherian X.obj.left := X.property.locallyNoetherian

/-- The actual open component is an object of the existing connected-base category. -/
def componentCMBase (X : DisBases) (c : _root_.ConnectedComponents X.obj.left) : Bases :=
  ⟨componentCMOver X.obj c, X.property.components c⟩

local notation "component" => componentCMBase D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality

/-- The restriction of a given actual base map to specified source and image
components, regarded in the existing connected admissible category. -/
def componentCMBaseHomTo {X Y : DisBases} (f : Y ⟶ X)
    (c : _root_.ConnectedComponents Y.obj.left) (d : _root_.ConnectedComponents X.obj.left)
    (e : componentMap f.hom.left c = d) :
    component Y c ⟶ component X d :=
  ObjectProperty.homMk (Over.homMk (componentHomTo f.hom.left c d e) (by
    change componentHomTo f.hom.left c d e ≫ (componentι X.obj.left d ≫ X.obj.hom) =
      componentι Y.obj.left c ≫ Y.obj.hom
    rw [componentHomTo_ι_assoc, Over.w]))

local notation "componentHom" => componentCMBaseHomTo D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality

omit [IsCMField F] [IsScalarTower ℚ F A] in
@[simp] theorem componentCMBaseHomTo_id (X : DisBases)
    (c : _root_.ConnectedComponents X.obj.left) :
    componentHom (𝟙 X) c c (componentMap_id X.obj.left c) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact componentHomTo_id c

omit [IsCMField F] [IsScalarTower ℚ F A] in
theorem componentCMBaseHomTo_comp {X Y Z : DisBases} (f : Y ⟶ X) (g : Z ⟶ Y)
    (c : _root_.ConnectedComponents Z.obj.left) (d : _root_.ConnectedComponents Y.obj.left)
    (e : _root_.ConnectedComponents X.obj.left)
    (hcd : componentMap g.hom.left c = d) (hde : componentMap f.hom.left d = e) :
    componentHom g c d hcd ≫ componentHom f d e hde =
      componentHom (g ≫ f) c e
        ((componentMap_comp g.hom.left f.hom.left c).trans
          ((congrArg (componentMap f.hom.left) hcd).trans hde)) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact componentHomTo_comp g.hom.left f.hom.left c d e hcd hde

local notation "tower" => unpointedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor
local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- Harris's product over the actual connected component schemes, at every
original Harris level. -/
def disconnectedClassTower (X : DisBases) : HarrisLevel D ⥤ Type 1 where
  obj U := ∀ c : _root_.ConnectedComponents X.obj.left, (tower (component X c)).obj U
  map k := ↾(fun v c => (tower (component X c)).map k (v c))
  map_id U := by
    ext v c
    exact ConcreteCategory.congr_hom ((tower (component X c)).map_id U) (v c)
  map_comp k l := by
    ext v c
    exact ConcreteCategory.congr_hom ((tower (component X c)).map_comp k l) (v c)

/-- Actual contravariant base pullback: select the image component and use the
already constructed pullback along its actual restricted morphism. -/
def disconnectedClassTowerPullback {X Y : DisBases} (f : Y ⟶ X) :
    disconnectedClassTower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h htor X ⟶
    disconnectedClassTower D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h htor Y where
  app U := ↾(fun v c =>
    ((pull (componentHom f c (componentMap f.hom.left c) rfl)).app U)
      (v (componentMap f.hom.left c)))
  naturality U V k := by
    ext v
    funext c
    exact
      (pull (componentHom f c (componentMap f.hom.left c) rfl)).naturality_apply k
      (v (componentMap f.hom.left c))

local notation "dispull" => disconnectedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "distower" => disconnectedClassTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor

/-- The pullback formula is valid at any equal specification of the image
component, so no representative or equality-transport convention is hidden. -/
theorem disconnectedClassTowerPullback_app_eq {X Y : DisBases} (f : Y ⟶ X)
    (U : HarrisLevel D) (v : (distower X).obj U)
    (c : _root_.ConnectedComponents Y.obj.left) (d : _root_.ConnectedComponents X.obj.left)
    (e : componentMap f.hom.left c = d) :
    ((dispull f).app U) v c = ((pull (componentHom f c d e)).app U) (v d) := by
  subst d
  rfl

@[simp] theorem disconnectedClassTowerPullback_id (X : DisBases) :
    dispull (𝟙 X) = 𝟙 (distower X) := by
  ext U v
  funext c
  change ((dispull (𝟙 X)).app U) v c = v c
  rw [disconnectedClassTowerPullback_app_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (𝟙 X) U v c c
    (componentMap_id X.obj.left c)]
  rw [componentCMBaseHomTo_id, unpointedClassTowerPullback_id]
  rfl

theorem disconnectedClassTowerPullback_comp {X Y Z : DisBases}
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    dispull f ≫ dispull g = dispull (g ≫ f) := by
  ext U v
  funext c
  let d := componentMap g.hom.left c
  let e := componentMap f.hom.left d
  have hcomp : componentMap (g ≫ f).hom.left c = e :=
    componentMap_comp g.hom.left f.hom.left c
  have k := unpointedClassTowerPullback_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    (componentHom f d e rfl) (componentHom g c d rfl)
  rw [componentCMBaseHomTo_comp] at k
  calc
    ((dispull f ≫ dispull g).app U) v c =
        ((pull (componentHom f d e rfl) ≫
          pull (componentHom g c d rfl)).app U) (v e) := rfl
    _ = ((pull (componentHom (g ≫ f) c e hcomp)).app U) (v e) := by
      exact congrArg
        (fun t : tower (component X e) ⟶ tower (component Z c) => t.app U (v e)) k
    _ = ((dispull (g ≫ f)).app U) v c :=
      (disconnectedClassTowerPullback_app_eq D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor (g ≫ f) U v c e hcomp).symm

/-- The actual disconnected tower presheaf, retaining all Harris transporter
maps and every actual morphism of the admissible base schemes. -/
def disconnectedClassTowerPresheaf : DisBasesᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) where
  obj X := distower X.unop
  map f := dispull f.unop
  map_id X := disconnectedClassTowerPullback_id D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor X.unop
  map_comp f g := (disconnectedClassTowerPullback_comp D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor f.unop g.unop).symm

/-- On a connected base the product evaluates isomorphically at any actual
component. The isomorphism is natural in every Harris transporter. -/
def disconnectedClassTowerComponentIso (X : DisBases) [PreconnectedSpace X.obj.left]
    (c : _root_.ConnectedComponents X.obj.left) :
    distower X ≅ tower (component X c) := by
  letI : Unique (_root_.ConnectedComponents X.obj.left) :=
    { default := c, uniq := fun _ => Subsingleton.elim _ _ }
  exact NatIso.ofComponents
    (fun U => (Equiv.piUnique (fun d => (tower (component X d)).obj U)).toIso)
    (by intros; rfl)

/-- The actual component inclusion, as an isomorphism of admissible CM bases
when the original base also has the named connected prerequisites. -/
def componentCMBaseInclusionIso (X : DisBases) (hX : admissible X.obj)
    (c : _root_.ConnectedComponents X.obj.left) :
    component X c ≅ (⟨X.obj, hX⟩ : Bases) := by
  letI : ConnectedSpace X.obj.left := hX.connected
  exact ObjectProperty.isoMk _
    (Over.isoMk (componentInclusionIso X.obj.left c) (by
      change (componentInclusionIso X.obj.left c).hom ≫ X.obj.hom =
        componentι X.obj.left c ≫ X.obj.hom
      rw [componentInclusionIso_hom]))

/-- Agreement with the original connected tower through the actual component
inclusion and actual contravariant base pullback. -/
def disconnectedClassTowerConnectedIso (X : DisBases) (hX : admissible X.obj)
    (c : _root_.ConnectedComponents X.obj.left) :
    distower X ≅ tower (⟨X.obj, hX⟩ : Bases) := by
  letI : ConnectedSpace X.obj.left := hX.connected
  exact disconnectedClassTowerComponentIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h htor X c ≪≫
    (unpointedClassTowerPresheaf D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality polarizationStability
      compatibility h htor).mapIso
        (componentCMBaseInclusionIso D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality X hX c).symm.op

/-- An empty base has exactly the empty-product value at every Harris level. -/
abbrev disconnectedClassTowerEmptyUnique (X : DisBases) [IsEmpty X.obj.left]
    (U : HarrisLevel D) : Unique ((distower X).obj U) := by
  letI := componentIndex_isEmpty X.obj.left
  exact
    { default := fun c => isEmptyElim c
      uniq := fun v => funext (fun c => isEmptyElim c) }

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
