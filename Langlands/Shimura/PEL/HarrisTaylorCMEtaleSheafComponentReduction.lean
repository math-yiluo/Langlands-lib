import Langlands.Shimura.PEL.HarrisTaylorCMConnectedEtaleSheafStatement
import Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof

/-! # Étale descent of the normalized CM classes from connected admissible tests -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

/-- A scheme map into an actual component scheme induces the constant map onto
that component on connected components. -/
theorem componentMap_comp_componentι {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    (d : _root_.ConnectedComponents X) (a : Y ⟶ componentScheme X d)
    (c : _root_.ConnectedComponents Y) :
    componentMap (a ≫ componentι X d) c = d := by
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentMap_mk, Scheme.Hom.comp_apply]
  exact (a y).2

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

local notation "Bases" => AdmissibleCMBaseCategory D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "DisBases" => ComponentwiseAdmissibleCMBaseCategory D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "component" => componentCMBase D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality
local notation "componentHom" => componentCMBaseHomTo D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "tower" => unpointedClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor
local notation "pull" => unpointedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
local notation "distower" => disconnectedClassTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h htor
local notation "dispull" => disconnectedClassTowerPullback D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor

/-- A connected admissible test, regarded as a componentwise admissible test. -/
def connectedCMTest (Z : Bases) : DisBases :=
  ⟨Z.obj, componentwiseAdmissibleCMBase_of_relativeDual D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0} Z.obj⟩

/-- A morphism from a connected test into an actual component of a test,
followed by the inclusion of that component. -/
def componentSourceHom (X : DisBases) (d : _root_.ConnectedComponents X.obj.left)
    (Z : Bases) (a : Z ⟶ component X d) :
    connectedCMTest D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality Z ⟶ X :=
  ObjectProperty.homMk (Over.homMk (a.hom.left ≫ componentι X.obj.left d) (by
    change (a.hom.left ≫ componentι X.obj.left d) ≫ X.obj.hom = Z.obj.hom
    rw [Category.assoc]
    exact Over.w a.hom))

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- The component restriction of `componentSourceHom` is the given morphism,
after the canonical identification of the sole component of a connected test. -/
theorem componentCMBaseHomTo_componentSourceHom (X : DisBases)
    (d : _root_.ConnectedComponents X.obj.left) (Z : Bases) (a : Z ⟶ component X d)
    (z : _root_.ConnectedComponents Z.obj.left)
    (e : componentMap (componentSourceHom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality X d Z a).hom.left z = d) :
    componentHom (componentSourceHom D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality X d Z a) z d e =
      (componentCMBaseInclusionIso D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality
        (connectedCMTest D C preservation composition unitCoherence associativity comparison
          symmetry stability square universality Z) Z.property z).hom ≫ a := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  symm
  refine componentHomTo_unique _ z d e _ ?_
  change ((componentInclusionIso Z.obj.left z).hom ≫ a.hom.left) ≫ componentι X.obj.left d =
    componentι Z.obj.left z ≫ (a.hom.left ≫ componentι X.obj.left d)
  rw [componentInclusionIso_hom, Category.assoc]

/-- Pullback of classes along an isomorphism of connected tests is injective. -/
theorem unpointedClassTowerPullback_app_injective_of_iso {X Y : Bases} (e : X ≅ Y)
    (V : HarrisLevel D) : Function.Injective ((pull e.hom).app V) := by
  intro p q hpq
  have k := unpointedClassTowerPullback_comp D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor e.hom e.inv
  rw [e.inv_hom_id, unpointedClassTowerPullback_id] at k
  have kp := congrArg (fun t => t.app V p) k
  have kq := congrArg (fun t => t.app V q) k
  simp only [NatTrans.comp_app, NatTrans.id_app] at kp kq
  have := congrArg ((pull e.inv).app V) hpq
  simp only [types_comp_apply, types_id_apply] at kp kq
  rw [← kp, ← kq]
  exact this

/-- Pullback of a disconnected class along `componentSourceHom`, evaluated at any
component of the connected test. -/
theorem disconnectedClassTowerPullback_componentSourceHom_apply (X : DisBases)
    (d : _root_.ConnectedComponents X.obj.left) (Z : Bases) (a : Z ⟶ component X d)
    (V : HarrisLevel D) (v : (distower X).obj V) (z : _root_.ConnectedComponents Z.obj.left) :
    (dispull (componentSourceHom D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality X d Z a)).app V v z =
      (pull (componentCMBaseInclusionIso D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (connectedCMTest D C preservation composition unitCoherence associativity comparison
          symmetry stability square universality Z) Z.property z).hom).app V
        ((pull a).app V (v d)) := by
  have e : componentMap (componentSourceHom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality X d Z a).hom.left z = d :=
    componentMap_comp_componentι d a.hom.left z
  refine (disconnectedClassTowerPullback_app_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor (componentSourceHom D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality X d Z a)
    V v z d e).trans ?_
  rw [componentCMBaseHomTo_componentSourceHom D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality X d Z a z e,
    ← unpointedClassTowerPullback_comp D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor]
  rfl

/-- Étale descent on connected admissible tests implies étale descent for the
normalized class presheaf on all componentwise admissible tests. -/
theorem cmSmallLevelEtaleSheafStatement_of_connected
    (hconn : CMConnectedEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor) :
    CMSmallLevelEtaleSheafStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := by
  intro U S J T f hf hsurj
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- The pieces of the cover lying over one actual component of `S`.
  let K : _root_.ConnectedComponents S.obj.left → Type := fun c =>
    Σ i : J, {d : _root_.ConnectedComponents (T i).obj.left //
      componentMap (f i).hom.left d = c}
  let W : ∀ c, K c → Bases := fun c k => component (T k.1) k.2.1
  let g : ∀ c (k : K c), W c k ⟶ component S c := fun c k =>
    componentHom (f k.1) k.2.1 c k.2.2
  have hcomp : ∀ c, ∃! w : (tower (component S c)).obj U.obj,
      ∀ k : K c, (pull (g c k)).app U.obj w = x k.1 k.2.1 := by
    intro c
    have hsheaf := hconn U (component S c) (K c) (W c) (g c) (by
      intro k
      have := hf k.1
      change Etale (componentHomTo (f k.1).hom.left k.2.1 c k.2.2)
      unfold componentHomTo
      infer_instance) (by
      intro p
      obtain ⟨i, y, hy⟩ := hsurj ((componentι S.obj.left c).base p)
      have hd : componentMap (f i).hom.left (ConnectedComponents.mk y) = c := by
        rw [componentMap_mk, hy]
        exact p.2
      refine ⟨⟨i, ConnectedComponents.mk y, hd⟩, ⟨y, rfl⟩, ?_⟩
      apply (componentι S.obj.left c).isOpenEmbedding.injective
      change (componentHomTo (f i).hom.left (ConnectedComponents.mk y) c hd ≫
        componentι S.obj.left c) _ = _
      rw [componentHomTo_ι, Scheme.Hom.comp_apply]
      exact hy)
    rw [Presieve.isSheafFor_arrows_iff] at hsheaf
    refine hsheaf (fun k => x k.1 k.2.1) ?_
    rintro ⟨i, d, hd⟩ ⟨j, e, he⟩ Z a b hab
    obtain ⟨z⟩ := (inferInstance : Nonempty Z.obj.left)
    let a' := componentSourceHom D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality (T i) d Z a
    let b' := componentSourceHom D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality (T j) e Z b
    have hab' : a' ≫ f i = b' ≫ f j := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      have k := congrArg (fun φ => φ.hom.left ≫ componentι S.obj.left c) hab
      change (a.hom.left ≫ componentHomTo (f i).hom.left d c hd) ≫ componentι S.obj.left c =
        (b.hom.left ≫ componentHomTo (f j).hom.left e c he) ≫ componentι S.obj.left c at k
      simp only [Category.assoc, componentHomTo_ι] at k
      change (a.hom.left ≫ componentι (T i).obj.left d) ≫ (f i).hom.left =
        (b.hom.left ≫ componentι (T j).obj.left e) ≫ (f j).hom.left
      simpa only [Category.assoc] using k
    have k := congrFun (hx i j _ a' b' hab') (ConnectedComponents.mk z)
    change (dispull a').app U.obj (x i) (ConnectedComponents.mk z) =
      (dispull b').app U.obj (x j) (ConnectedComponents.mk z) at k
    rw [disconnectedClassTowerPullback_componentSourceHom_apply,
      disconnectedClassTowerPullback_componentSourceHom_apply] at k
    exact unpointedClassTowerPullback_app_injective_of_iso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor _ U.obj k
  choose w hw hwu using hcomp
  refine ⟨w, ?_, ?_⟩
  · intro i
    funext d
    exact hw _ ⟨i, d, rfl⟩
  · intro t ht
    funext c
    apply hwu c
    rintro ⟨i, d, rfl⟩
    exact congrFun (ht i) d

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
