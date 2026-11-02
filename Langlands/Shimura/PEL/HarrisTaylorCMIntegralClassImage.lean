import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClasses

/-! # Integral-action representatives and their exact normalized CM class image -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
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
  {S : Scheme.{0}}
  (p : S ⟶ Spec (.of F))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "reflexStructure" => D.harrisTaylorReflexStructure C p
local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
local notation "Num" => NumericalObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "mkClass" => classOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "jointProof" => determinantDimensionCondition_iff D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality p
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "Restriction" => PolarizedWeilLevel.IntegralActionRestriction preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "IntegralMult" => PolarizedWeilLevel.IntegralPolarizedMultiple preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "restore" => PolarizedWeilLevel.multiple_iff_integralPolarizedMultiple
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality basisO additivity
local notation "transport" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity

local notation "Classes" => HarrisNumericalWeilLevel.IsoClass D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "mapRep" => HarrisNumericalWeilLevel.mapRepresentative D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  compatibility h s hs htor hu
local notation "mapClass" => HarrisNumericalWeilLevel.classMap D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality reflexStructure
  compatibility h s hs htor hu additivity L p
local notation "tower" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  reflexStructure compatibility h s hs htor hu additivity L p

/-- An actual normalized representative with an integral action on the same scheme. -/
structure IntegralCMRepresentative (U : HarrisLevel D) where
  data : Data U
  condition : letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C p
      data.1.actionObj.abelianScheme data.1.actionObj.action
  restriction : letI := auxiliaryStarRing D C; Restriction O data.1

local notation "Rep" => IntegralCMRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor hu

/-- Forget the supplied integral action into the exact existing normalized CM class. -/
def integralCMRepresentativeClass {U : HarrisLevel D} (x : Rep U) : Classes U := by
  let := auxiliaryStarRing D C
  exact mkClass x.data ((jointProof x.data.1).mp x.condition).1
    ((jointProof x.data.1).mp x.condition).2

local notation "repClass" => integralCMRepresentativeClass D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu additivity

/-- The original rational-isogeny orbit relation, expressed by exact integral witnesses. -/
def IntegralCMRelated {U : HarrisLevel D} (x y : Rep U) : Prop :=
  letI := auxiliaryStarRing D C
  ∃ (q : ℚˣ) (e : x.data.1.actionObj ≅ y.data.1.actionObj)
    (hd : IntegralMult x.data.1 y.data.1 x.restriction y.restriction q e),
    transport x.data.1 y.data.1 ((hodgeLevelFunctor D C).obj U) q e
      ((restore x.data.1 y.data.1 x.restriction y.restriction q e).mpr hd)
      x.data.2 = y.data.2

local notation "Related" => IntegralCMRelated D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

/-- No integral lift choice changes which original normalized classes are equal. -/
theorem integralCMRelated_iff_class_eq {U : HarrisLevel D} (x y : Rep U) :
    Related x y ↔ repClass x = repClass y := by
  let := auxiliaryStarRing D C
  exact (classOf_eq_iff_integralPolarizedMultiple D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h s hs
    htor hu additivity x.data y.data x.condition y.condition x.restriction y.restriction).symm

local notation "relIff" => integralCMRelated_iff_class_eq D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu additivity

/-- The exact integral-witness relation is an equivalence relation. -/
def integralCMSetoid (U : HarrisLevel D) : Setoid (Rep U) where
  r := Related
  iseqv := ⟨fun x => (relIff x x).mpr rfl,
    fun {x y} hxy => (relIff y x).mpr ((relIff x y).mp hxy).symm,
    fun {x y z} hxy hyz =>
      (relIff x z).mpr (((relIff x y).mp hxy).trans ((relIff y z).mp hyz))⟩

local notation "rel" => integralCMSetoid D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

/-- Integral-action representatives modulo the original rational-isogeny relation. -/
def IntegralCMIsoClass (U : HarrisLevel D) := Quotient (rel U)

local notation "IClasses" => IntegralCMIsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

/-- Form the class of an actual representative with its supplied integral action. -/
def integralCMClassOf {U : HarrisLevel D} (x : Rep U) : IClasses U := Quotient.mk _ x

local notation "imk" => integralCMClassOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

/-- Equality in the new quotient uses precisely the displayed integral witnesses. -/
theorem integralCMClassOf_eq_iff {U : HarrisLevel D} (x y : Rep U) :
    imk x = imk y ↔ Related x y := Quotient.eq

/-- Forgetting descends through exactly the original normalized equivalence relation. -/
def integralCMForget {U : HarrisLevel D} : IClasses U → Classes U :=
  Quotient.lift repClass (fun x y hxy => (relIff x y).mp hxy)

local notation "forget" => integralCMForget D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

@[simp] theorem integralCMForget_classOf {U : HarrisLevel D} (x : Rep U) :
    forget (imk x) = repClass x := rfl

/-- The integral formulation creates no extra identifications and no duplicate classes. -/
theorem integralCMForget_injective {U : HarrisLevel D} :
    Function.Injective (forget : IClasses U → Classes U) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  exact Quotient.sound ((relIff a b).mpr hab)

local notation "forgetInjective" => integralCMForget_injective D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu additivity

/-- A normalized rational class lies in the integral image if it has such a representative. -/
def IntegralCMClassCondition {U : HarrisLevel D} (q : Classes U) : Prop :=
  ∃ x : Rep U, repClass x = q

local notation "ImageCondition" => IntegralCMClassCondition D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu additivity

/-- The actual image inside the existing normalized CM classes, without an existence premise. -/
def IntegralCMClassImage (U : HarrisLevel D) := {q : Classes U // ImageCondition q}

local notation "Image" => IntegralCMClassImage D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

/-- The forgetful map factors through exactly its image. -/
def integralCMForgetToImage {U : HarrisLevel D} (q : IClasses U) : Image U :=
  ⟨forget q, Quotient.inductionOn q (fun x => ⟨x, rfl⟩)⟩

local notation "toImage" => integralCMForgetToImage D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu additivity

/-- Integral-witness classes are equivalent to the exact image in the original moduli set. -/
def integralCMClassImageEquiv (U : HarrisLevel D) : IClasses U ≃ Image U :=
  Equiv.ofBijective toImage ⟨fun x y hxy => forgetInjective (congrArg Subtype.val hxy), by
    rintro ⟨q, x, hx⟩
    exact ⟨imk x, Subtype.ext hx⟩⟩

local notation "imageEquiv" => integralCMClassImageEquiv D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu additivity

@[simp] theorem integralCMClassImageEquiv_val {U : HarrisLevel D} (q : IClasses U) :
    (imageEquiv U q).val = forget q := rfl

/-- An original Harris transporter changes only the orbit, retaining the actual integral action. -/
def integralCMRepresentativeMap {U V : HarrisLevel D} (f : U ⟶ V) (x : Rep U) : Rep V := by
  let := auxiliaryStarRing D C
  exact ⟨mapRep f x.data, x.condition, x.restriction⟩

local notation "imapRep" => integralCMRepresentativeMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu

@[simp] theorem integralCMRepresentativeClass_map {U V : HarrisLevel D}
    (f : U ⟶ V) (x : Rep U) : repClass (imapRep f x) = mapClass f (repClass x) := rfl

/-- The exact integral-witness relation is preserved by every original transporter. -/
theorem integralCMRelated_map {U V : HarrisLevel D} (f : U ⟶ V)
    (x y : Rep U) (hxy : Related x y) : Related (imapRep f x) (imapRep f y) :=
  (relIff _ _).mpr (congrArg (mapClass f) ((relIff x y).mp hxy))

/-- All original Harris level arrows act on integral-witness classes. -/
def integralCMClassMap {U V : HarrisLevel D} (f : U ⟶ V) : IClasses U → IClasses V :=
  Quotient.map (imapRep f) (integralCMRelated_map D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality p compatibility h s hs htor
    hu additivity f)

local notation "imapClass" => integralCMClassMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

@[simp] theorem integralCMForget_classMap {U V : HarrisLevel D}
    (f : U ⟶ V) (q : IClasses U) :
    forget (imapClass f q) = mapClass f (forget q) := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The quotient comparison retains the full original transporter level category. -/
def integralCMClassTower : HarrisLevel D ⥤ Type 1 where
  obj := IClasses
  map f := ↾(imapClass f)
  map_id U := by
    ext q
    apply forgetInjective
    change forget (imapClass (𝟙 U) q) = forget q
    rw [integralCMForget_classMap]
    exact ConcreteCategory.congr_hom ((tower).map_id U) (forget q)
  map_comp f g := by
    ext q
    apply forgetInjective
    change forget (imapClass (f ≫ g) q) = forget (imapClass g (imapClass f q))
    simp only [integralCMForget_classMap]
    exact ConcreteCategory.congr_hom ((tower).map_comp f g) (forget q)

local notation "itower" => integralCMClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality p compatibility h s hs htor
  hu additivity

/-- The exact integral image is stable under every original Harris transporter. -/
theorem integralCMClassCondition_map {U V : HarrisLevel D} (f : U ⟶ V)
    (q : Classes U) (hq : ImageCondition q) : ImageCondition (mapClass f q) := by
  obtain ⟨x, hx⟩ := hq
  exact ⟨imapRep f x, (integralCMRepresentativeClass_map D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality p
    compatibility h s hs htor hu additivity f x).trans (congrArg (mapClass f) hx)⟩

/-- The subimage is a genuine tower of subsets of the existing normalized CM classes. -/
def integralCMClassImageTower : HarrisLevel D ⥤ Type 1 where
  obj := Image
  map f := ↾(fun q => ⟨mapClass f q.val,
    integralCMClassCondition_map D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h s hs htor hu
      additivity f q.val q.property⟩)
  map_id U := by
    ext q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((tower).map_id U) q.val
  map_comp f g := by
    ext q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((tower).map_comp f g) q.val

local notation "imageTower" => integralCMClassImageTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality p
  compatibility h s hs htor hu additivity

/-- The exact quotient-to-image comparison is natural for all original level arrows. -/
def integralCMClassImageTowerIso : itower ≅ imageTower :=
  NatIso.ofComponents (fun U => (imageEquiv U).toIso) (by
    intro U V f
    ext q
    apply Subtype.ext
    exact integralCMForget_classMap D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality p compatibility h s hs htor hu additivity f q)

/-- The image embeds naturally in the original normalized moduli tower. -/
def integralCMClassImageInclusion : imageTower ⟶ tower where
  app _ := ↾Subtype.val
  naturality _ _ _ := rfl

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
